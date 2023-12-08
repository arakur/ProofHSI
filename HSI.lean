/-
  # Tarski's High School Algebra Problem

  **Tarski の高校代数問題**(加法・乗法・累乗で表された正整数の恒等式は，加法・乗法・累乗の基本法則のみを用いて証明できるか？)の反例となる Wilkie の等式を定義し，それが実際に反例であることを Burris-Yean の構成した有限モデルを用いて証明する．
-/

-- 準備．

section Preliminaries

  /-! theorem のシノニム． -/
  macro mods:declModifiers "lemma" n:declId sig:declSig val:declVal : command => `($mods:declModifiers theorem $n $sig $val)

  -- 自然数に関する補題．

  /-! Nat の別名． -/
  abbrev ℕ := Nat

  namespace Nat

    lemma one_pow (n : ℕ) : 1 ^ n = 1 :=
      by induction n with
      | zero => rw [pow_zero]
      | succ n ih => rw [pow_succ, ih]

    lemma pow_add (a b c : ℕ) : a ^ (b + c) = a ^ b * a ^ c :=
      by induction b with
      | zero => rw [Nat.zero_add, pow_zero, Nat.one_mul]
      | succ b ih => calc
        a ^ (succ b + c)
        _ = a ^ b * a ^ c * a := by rw [Nat.succ_add, pow_succ, ih]
        _ = a ^ b * (a ^ c * a) := by rw [Nat.mul_assoc]
        _ = a ^ b * (a * a ^ c) := by congr 1; rw [Nat.mul_comm]
        _ = a ^ b * a * a ^ c := by rw [Nat.mul_assoc]

    lemma pow_mul (a b c : ℕ) : a ^ (b * c) = (a ^ b) ^ c :=
      by induction c with
      | zero => rw [pow_zero, Nat.mul_zero, pow_zero]
      | succ c ih => calc
        a ^ (b * succ c)
        _ = a ^ (b * c + b) := by rw [Nat.mul_succ]
        _ = a ^ (b * c) * a ^ b := by rw [pow_add]
        _ = (a ^ b) ^ c * a ^ b := by rw [ih]
        _ = (a ^ b) ^ succ c := by rw [pow_succ]

    lemma mul_pow (a b c : ℕ) : (a * b) ^ c = a ^ c * b ^ c :=
      by induction c with
      | zero => rw [pow_zero, pow_zero, pow_zero]
      | succ c ih => calc
        (a * b) ^ succ c
        _ = (a * b) ^ c * (a * b) := by rw [pow_succ]
        _ = a ^ c * b ^ c * (a * b) := by rw [ih]
        _ = a ^ c * (a * b * b ^ c) := by rw [Nat.mul_assoc]; congr 1; rw [Nat.mul_comm]
        _ = a ^ c * (a * (b * b ^ c)) := by congr 1; rw [Nat.mul_assoc]
        _ = a ^ c * a * (b ^ c * b) := by rw [Nat.mul_assoc]; congr 2; rw [Nat.mul_comm]
        _ = a ^ succ c * b ^ succ c := by rw [pow_succ, pow_succ]

      lemma zero_pow (n : ℕ) : n ≠ 0 → 0 ^ n = 0 := by
        intro (h : n ≠ 0)
        cases n with
        | zero => contradiction
        | succ n => rw [pow_succ, Nat.mul_zero]

      lemma pow_one (n : ℕ) : n ^ 1 = n := by rw [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]

      lemma pow_two (n : ℕ) : n ^ 2 = n * n := by rw [Nat.pow_succ, Nat.pow_one]

      lemma pow_three (n : ℕ) : n ^ 3 = n * n * n := by rw [Nat.pow_succ, Nat.pow_two]

      lemma pow_four (n : ℕ) : n ^ 4 = n * n * n * n := by rw [Nat.pow_succ, Nat.pow_three]

      lemma pow_succ_succ_ge_pow_succ (n m : ℕ) : n ^ succ (succ m) ≥ n ^ succ m := by cases n with
        | zero => simp [Nat.pow_succ]
        | succ n => calc
          (succ n) ^ succ (succ m)
          _ = (succ n) ^ succ m * (succ n) := by rw [Nat.pow_succ]
          _ ≥ (succ n) ^ succ m * 1 := by exact Nat.mul_le_mul_left _ (Nat.le_add_left _ _)
          _ = (succ n) ^ succ m := by rw [Nat.mul_one]

      lemma pow_two_ge_self (n : ℕ) : n ^ 2 ≥ n := calc
        n = n ^ 1 := by rw [Nat.pow_one]
        _ ≤ n ^ 2 := by exact Nat.pow_succ_succ_ge_pow_succ _ _

      lemma pow_three_ge_pow_two (n : ℕ) : n ^ 3 ≥ n ^ 2 :=
        Nat.pow_succ_succ_ge_pow_succ _ _

      lemma pow_four_ge_pow_three (n : ℕ) : n ^ 4 ≥ n ^ 3 :=
        Nat.pow_succ_succ_ge_pow_succ _ _

  end Nat

end Preliminaries

section Definitions

  /-! 加法・乗法・累乗で構成された式．-/
  inductive HSExpr :=
    | One
    | Plus (A : HSExpr) (B : HSExpr)
    | Times (A : HSExpr) (B : HSExpr)
    | Power (A : HSExpr) (B : HSExpr)
    | Var (name: String)

  namespace HSExpr
    -- 自然数を HSExpr として扱う．0 は HSExpr に含まれないため，便宜上 1 として扱う．

    def ofNat (n : ℕ) : HSExpr := match n with
      | 0 | 1 => One
      | n + 1 => Plus (ofNat n) One

    instance : OfNat HSExpr n := ⟨ofNat n⟩

    -- 加法 `+`，乗法 `*`，累乗 `↑` の記号を導入する．

    instance : HAdd HSExpr HSExpr HSExpr := ⟨Plus⟩
    instance : HMul HSExpr HSExpr HSExpr := ⟨Times⟩

    infixr :80 " ↑ " => Power

    /-! 変数に対する割り当て． -/
    def Assign := String → ℕ

    /-! 式を評価する． -/
    @[simp]
    def eval (a: Assign) : HSExpr → ℕ
      | One => 1
      | A + B => A.eval a + B.eval a
      | A * B => A.eval a * B.eval a
      | Power A B => A.eval a ^ B.eval a
      | Var name => a name

    notation "⟦" A ";" σ "⟧" => HSExpr.eval σ A

    /-! *High school identities* により証明可能な等価性． -/
    inductive peq : HSExpr -> HSExpr -> Prop
      -- 同値関係
      | refl :
        peq A A
      | symm :
        peq A B -> peq B A
      | trans :
        peq A B -> peq B C -> peq A C
      -- 代入原理
      | add_congr :
        peq A A' -> peq B B' -> peq (A + B) (A' + B')
      | mul_congr :
        peq A A' -> peq B B' -> peq (A * B) (A' * B')
      | pow_congr :
        peq A A' -> peq B B' -> peq (A ↑ B) (A' ↑ B')
      -- *High school identities*
      | add_comm :
        peq (A + B) (B + A)
      | add_assoc :
        peq (A + B + C) (A + (B + C))
      | mul_comm :
        peq (A * B) (B * A)
      | mul_assoc :
        peq (A * B * C) (A * (B * C))
      | mul_one :
        peq (A * 1) A
      | mul_add :
        peq (A * (B + C)) (A * B + A * C)
      | pow_one :
        peq (A ↑ 1) A
      | one_pow :
        peq (1 ↑ A) 1
      | pow_add :
        peq (A ↑ (B + C)) (A ↑ B * A ↑ C)
      | pow_mul :
        peq (A ↑ (B * C)) ((A ↑ B) ↑ C)
      | mul_pow :
        peq ((A * B) ↑ C) (A ↑ C * B ↑ C)

    infix:50 " ≈ " => HSExpr.peq

    instance peq.inst_trans : Trans peq peq peq := ⟨peq.trans⟩

    -- いくつか補題を示しておく．

    namespace peq

    lemma one_mul : 1 * A ≈ A := calc
      1 * A
      _ ≈ A * 1 := mul_comm
      _ ≈ A     := mul_one

    lemma add_mul : (A + B) * C ≈ A * C + B * C := calc
      (A + B) * C
      _ ≈ C * (A + B)     := mul_comm
      _ ≈ C * A + C * B   := mul_add
      _ ≈ A * C + B * C   := add_congr mul_comm mul_comm

    lemma two_mul : 2 * A ≈ A + A := calc
      2 * A
      _ ≈ (1 + 1) * A     := mul_congr refl refl
      _ ≈ 1 * A + 1 * A   := add_mul
      _ ≈ A + A           := add_congr one_mul one_mul

    lemma pow_two : A ↑ 2 ≈ A * A := calc
      A ↑ 2
      _ ≈ A ↑ (1 + 1)     := pow_congr refl refl
      _ ≈ A ↑ 1 * A ↑ 1   := pow_add
      _ ≈ A * A           := mul_congr pow_one pow_one

    -- 基本法則と補題から (x + 1) ↑ 2 ≈ x ↑ 2 + 2 * x + 1 が証明できる．

    example :
      (x + 1) ↑ 2 ≈ x ↑ 2 + 2 * x + 1
      := by
      calc
        (x + 1) ↑ 2
        _ ≈ (x + 1) ↑ (1 + 1)                 := pow_congr refl refl
        _ ≈ (x + 1) ↑ 1 * (x + 1) ↑ 1         := pow_add
        _ ≈ (x + 1) * (x + 1)                 := mul_congr pow_one pow_one
        _ ≈ x * (x + 1) + 1 * (x + 1)         := add_mul
        _ ≈ (x * x + x * 1) + (1 * x + 1 * 1) := add_congr mul_add mul_add
        _ ≈ (x * x + x) + (x + 1)             := add_congr
                                                  (add_congr mul_comm mul_one)
                                                  (add_congr one_mul mul_one)
        _ ≈ x * x + (x + (x + 1))             := add_assoc
        _ ≈ x * x + (x + x + 1)               := add_congr
                                                  refl
                                                  (symm add_assoc)
        _ ≈ x * x + (2 * x + 1)               := add_congr
                                                  refl
                                                  (add_congr (symm two_mul) refl)
        _ ≈ x * x + 2 * x + 1                 := symm add_assoc
        _ ≈ x ↑ 2 + 2 * x + 1                 := add_congr
                                                  (add_congr (symm pow_two) refl)
                                                  refl

    end peq

    /-! HSExpr の関数としての等価性． -/
    @[simp]
    def equiv A B := ∀ σ, ⟦A; σ⟧ = ⟦B; σ⟧

    infix: 50 " ≡ " => HSExpr.equiv

    /-! HSI の下で等価な2つの式は関数として等価． -/
    lemma peq.sound : A ≈ B → A ≡ B := by
      intro (h: A ≈ B)
      intro σ; show ⟦A; σ⟧ = ⟦B; σ⟧
      induction h
      case refl | symm | trans => simp [*]
      case add_congr | mul_congr | pow_congr => simp; congr
      case add_comm => exact Nat.add_comm _ _
      case add_assoc => exact Nat.add_assoc _ _ _
      case mul_comm => exact Nat.mul_comm _ _
      case mul_assoc => exact Nat.mul_assoc _ _ _
      case mul_one => exact Nat.mul_one _
      case mul_add => exact Nat.mul_add _ _ _
      case pow_one => simp [Nat.pow_succ, Nat.pow_zero]
      case one_pow => exact Nat.one_pow _
      case pow_add => exact Nat.pow_add _ _ _
      case pow_mul => exact Nat.pow_mul _ _ _
      case mul_pow => exact Nat.mul_pow _ _ _

  end HSExpr

end Definitions

section WilkieIdentity

/-
  # Wilkie の等式

  **Wilkie の等式**は，以下に定義される `A`, `B`, `C`, `D` によって

      `  (A ↑ x + B ↑ x) ↑ y * (C ↑ y + D ↑ y) ↑ x`
      `= (A ↑ y + B ↑ y) ↑ x * (C ↑ x + D ↑ x) ↑ y`

  と表される式である．
-/

  /-! Wilkie の等式の定義． -/
  namespace Wilkie
    open HSExpr

    abbrev x := Var "x"
    abbrev y := Var "y"

    abbrev A := x + 1
    abbrev B := x ↑ 2 + x + 1
    abbrev C := x ↑ 3 + 1
    abbrev D := x ↑ 4 + x ↑ 2 + 1

    abbrev W₁ : HSExpr := (A ↑ x + B ↑ x) ↑ y * (C ↑ y + D ↑ y) ↑ x
    abbrev W₂ : HSExpr := (A ↑ y + B ↑ y) ↑ x * (C ↑ x + D ↑ x) ↑ y

    -- 補題を示す．

    lemma A_eval_mul_E_eq_C_eval (x : ℕ) :
      (x + 1) * (x ^ 2 - x + 1) = x ^ 3 + 1
      := calc
      (x + 1) * (x ^ 2 - x + 1)
      _ = x ^ 3 - x ^ 2 + (x + (x ^ 2 - x)) + 1
        := by
          rw [Nat.add_mul, Nat.mul_add, Nat.mul_sub_left_distrib]
          repeat rw [Nat.pow_succ]
          repeat rw [Nat.pow_zero]
          repeat rw [Nat.mul_assoc]
          repeat rw [Nat.mul_one]
          repeat rw [Nat.one_mul]
          repeat rw [Nat.add_assoc]
      _ = x ^ 3 - x ^ 2 + (x ^ 2 - x + x) + 1
        := by rw [Nat.add_comm x]
      _ = x ^ 3 + 1
        := by
          rw [Nat.sub_add_cancel, Nat.sub_add_cancel]
          exact Nat.pow_three_ge_pow_two x
          exact Nat.pow_two_ge_self x

    lemma B_eval_mul_E_eq_D_eval (x : ℕ) :
      (x ^ 2 + x + 1) * (x ^ 2 - x + 1) = x ^ 4 + x ^ 2 + 1
      := calc
      (x ^ 2 + x + 1) * (x ^ 2 - x + 1)
      _ = x ^ 4 - x ^ 3 + x ^ 2 + (x ^ 3 - x ^ 2 + x) + (x ^ 2 - x + 1)
        := by
          rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]
          rw [Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.mul_one]
          repeat rw [Nat.mul_sub_left_distrib]
          repeat rw [Nat.pow_succ]
          rw [Nat.pow_zero, Nat.one_mul]
          repeat rw [Nat.mul_assoc]
      _ = x ^ 4 - x ^ 3 + (x ^ 2 + (x ^ 3 - x ^ 2)) + (x + (x ^ 2 - x)) + 1
        := by repeat rw [Nat.add_assoc]
      _ = x ^ 4 - x ^ 3 + (x ^ 3 - x ^ 2 + x ^ 2) + (x ^ 2 - x + x) + 1
        := by rw [Nat.add_comm x, Nat.add_comm (x ^ 2)]
      _ = x ^ 4 + x ^ 2 + 1
        := by
          repeat rw [Nat.sub_add_cancel]
          exact Nat.pow_two_ge_self x
          exact Nat.pow_four_ge_pow_three x
          exact Nat.pow_three_ge_pow_two x

  end Wilkie

  abbrev W₁ := Wilkie.W₁
  abbrev W₂ := Wilkie.W₂

  /-! Wilkie の等式の両辺は関数として等価である． -/
  theorem wilkie_equiv : W₁ ≡ W₂ := by
    intro σ; show ⟦W₁; σ⟧ = ⟦W₂; σ⟧
    simp [W₁, W₂]
    generalize σ "x" = x, σ "y" = y
    let A := x + 1
    let B := x ^ 2 + x + 1
    let C := x ^ 3 + 1
    let D := x ^ 4 + x ^ 2 + 1
    show
      (A ^ x + B ^ x) ^ y * (C ^ y + D ^ y) ^ x =
      (A ^ y + B ^ y) ^ x * (C ^ x + D ^ x) ^ y

    let E := x ^ 2 - x + 1
    have h₁ : A * E = C := Wilkie.A_eval_mul_E_eq_C_eval x
    have h₂ : B * E = D := Wilkie.B_eval_mul_E_eq_D_eval x
    rw [← h₁, ← h₂]
    show
      (A ^ x + B ^ x) ^ y * ((A * E) ^ y + (B * E) ^ y) ^ x =
      (A ^ y + B ^ y) ^ x * ((A * E) ^ x + (B * E) ^ x) ^ y

    rw [Nat.mul_pow, Nat.mul_pow, Nat.mul_pow, Nat.mul_pow]
    show
      (A ^ x + B ^ x) ^ y * (A ^ y * E ^ y + B ^ y * E ^ y) ^ x =
      (A ^ y + B ^ y) ^ x * (A ^ x * E ^ x + B ^ x * E ^ x) ^ y
    rw [← Nat.add_mul, ← Nat.add_mul]
    rw [Nat.mul_pow, Nat.mul_pow]
    rw [←Nat.mul_assoc, ←Nat.mul_assoc]
    show
      (A ^ x + B ^ x) ^ y * (A ^ y + B ^ y) ^ x *
      (E ^ y) ^ x =
      (A ^ y + B ^ y) ^ x * (A ^ x + B ^ x) ^ y *
      (E ^ x) ^ y
    have : (E ^ y) ^ x = (E ^ x) ^ y :=
      by rw [←Nat.pow_mul, ←Nat.pow_mul, Nat.mul_comm]
    rw [this]; congr 1
    show
      (A ^ x + B ^ x) ^ y * (A ^ y + B ^ y) ^ x =
      (A ^ y + B ^ y) ^ x * (A ^ x + B ^ x) ^ y
    exact Nat.mul_comm _ _

end WilkieIdentity

section BY12Algebra

/-
  ## Burris-Yean の有限モデル

  Wilkie の等式が HSI から導出できないことを示すために，Burris-Yean の構成した要素数 12 のモデルを用いる．このモデルは HSI をすべて満たし，なおかつ Wilkie の等式を満たさない．
-/

  /-! Burris-Yean の有限モデル． -/
  inductive BY12 :=
    | n₁ | n₂ | n₃ | n₄
    | a | b | c | d | e | f | g | h
    deriving Repr

  namespace BY12

    -- 12 個の要素に加法・乗法・累乗演算を定義する．

    instance : OfNat BY12 n := ⟨match n with
      | 1 => n₁
      | 2 => n₂
      | 3 => n₃
      | _ => n₄⟩

    @[simp]
    def add : BY12 → BY12 → BY12
      | 1, 1 | 1, a
      | a, 1
      => 2
      | 1, 2 | 1, b | 1, d | 1, e | 1, f | 1, g
      | 2, 1 | 2, a | 2, c
      | a, 2 | a, d | a, f | a, g
      | b, 1
      | c, 2 | c, d | c, e | c, f | c, g
      | d, 1 | d, a | d, c
      | e, 1 | e, c | e, f
      | f, 1 | f, a | f, c | f, e | f, g
      | g, 1 | g, a | g, c | g, f
      => 3
      | a, a | a, c | c, a | c, c
      => b
      | 1, c | c, 1
      => d
      | a, e | e, a | e, g | g, e
      => h
      | _, _ => 4

    instance : HAdd BY12 BY12 BY12 := ⟨add⟩

    @[simp]
    def mul : BY12 → BY12 → BY12
      | 1, y => y | s, 1 => s
      | 2, y => y + y | s, 2 => s + s
      | 3, y => y + y + y | s, 3 => s + s + s
      | a, b | b, a | b, c | c, b | a, d | d, a | c, d | d, c => b
      | a, a | a, c | c, a | c, c => c
      | a, e | e, a | e, g | g, e => h
      | _, _ => 4

    instance : HMul BY12 BY12 BY12 := ⟨mul⟩

    @[simp]
    def pow : BY12 → BY12 → BY12
      | 1, _ => 1
      | s, 1 => s
      | s, 2 => s * s
      | s, 3 => s * s * s
      | a, _ | c, _ => c
      | 3, a | 3, g => e
      | 2, e | d, a => f
      | 3, e => g
      | 3, h | e, e | g, a | g, g => h
      | _, _ => 4

    infixr:80 " ↑BY " => BY12.pow

    instance : DecidableEq BY12 := by
      intro s t
      show Decidable (s = t)
      cases s <;> cases t
      all_goals simp
      all_goals try exact Decidable.isTrue trivial
      all_goals try apply Decidable.isFalse (by intro; assumption)

    -- `BY12` に対して，HSI のすべての等式が成り立つことを証明する．

    lemma add_comm (s t : BY12) : s + t = t + s := by
      cases s <;> cases t <;> rfl

    lemma add_assoc (s t u : BY12) : (s + t) + u = s + (t + u) := by
      -- admit
      cases s <;> cases t <;> cases u <;> rfl

    lemma mul_comm (s t : BY12) : s * t = t * s := by
      cases s <;> cases t <;> rfl

    lemma mul_assoc (s t u : BY12) : (s * t) * u = s * (t * u) := by
      -- admit
      cases s <;> cases t <;> cases u <;> rfl

    lemma mul_one (s : BY12) : s * 1 = s := by
      cases s <;> rfl

    lemma mul_add (s t u : BY12) : s * (t + u) = s * t + s * u := by
      -- admit
      cases s <;> cases t <;> cases u <;> rfl

    lemma pow_one (s : BY12) : s ↑BY 1 = s := by
      cases s <;> rfl

    lemma one_pow (s : BY12) : 1 ↑BY s = 1 := by
      cases s <;> rfl

    lemma pow_add (s t u : BY12) : s ↑BY (t + u) = s ↑BY t * s ↑BY u := by
      -- admit
      cases s <;> cases t <;> cases u <;> rfl

    lemma pow_mul (s t u : BY12) : s ↑BY (t * u) = (s ↑BY t) ↑BY u := by
      -- admit
      cases s <;> cases t <;> cases u <;> rfl

    lemma mul_pow (s t u : BY12) : (s * t) ↑BY u = s ↑BY u * t ↑BY u := by
      -- admit
      cases s <;> cases t <;> cases u <;> rfl
  end BY12

  /-! `BY12` 値の変数の割り当て． -/
  def AssignBY12 := String → BY12

  /-! `BY12` 値での式の評価． -/
  @[simp]
  def HSExpr.evalBY12 (σ : AssignBY12) : HSExpr → BY12
    | One => 1
    | A + B => A.evalBY12 σ + B.evalBY12 σ
    | A * B => A.evalBY12 σ * B.evalBY12 σ
    | Power A B => A.evalBY12 σ ↑BY B.evalBY12 σ
    | Var name => σ name

  notation "⟦" A ";" σ "⟧BY" => HSExpr.evalBY12 σ A

  /-! `BY12` 値関数としての等価性． -/
  @[simp]
  def HSExpr.equiv_by A B := ∀ σ, ⟦A; σ⟧BY = ⟦B; σ⟧BY

  infix: 50 " ≡BY " => HSExpr.equiv_by

end BY12Algebra

section MainProof

/-!
## 証明

以上を用いて，Wilkie の等式が HSI から導出できないことを証明する．
-/

  /-! HSI の下で等価な2つの式は `BY12` 値関数として等価． -/
  lemma peq.sound_by : A ≈ B → A ≡BY B := by
    intro h σ; show ⟦A; σ⟧BY = ⟦B; σ⟧BY
    induction h
    case refl | symm | trans => simp [*]
    case add_congr | mul_congr | pow_congr => simp; congr
    case add_comm => exact BY12.add_comm _ _
    case add_assoc => exact BY12.add_assoc _ _ _
    case mul_comm => exact BY12.mul_comm _ _
    case mul_assoc => exact BY12.mul_assoc _ _ _
    case mul_one => exact BY12.mul_one _
    case mul_add => exact BY12.mul_add _ _ _
    case pow_one => exact BY12.pow_one _
    case one_pow => exact BY12.one_pow _
    case pow_add => exact BY12.pow_add _ _ _
    case pow_mul => exact BY12.pow_mul _ _ _
    case mul_pow => exact BY12.mul_pow _ _ _

  /-! `BY12` において Wilkie の等式は成り立たない． -/
  lemma Wilkie.BY12_not_hold : ¬ W₁ ≡BY W₂ := by
    intro (h: W₁ ≡BY W₂)
    let σ | "x" => BY12.a | "y" => BY12.e | _ => 1
    specialize h σ
    contradiction

  /-! HSI から Wilkie の等式は導出できない． -/
  theorem Wilkie.not_peq : ¬ W₁ ≈ W₂ :=
    Wilkie.BY12_not_hold ∘ peq.sound_by

  /-! 特に，HSI は正整数において成り立つ HSExpr の全ての等式を証明することができない． -/
  theorem HSExpr.peq.not_complete : ¬ ∀ A B, A ≡ B → A ≈ B := by
    intro (h : ∀ A B, A ≡ B → A ≈ B)
    have : W₁ ≈ W₂ := h W₁ W₂ wilkie_equiv
    have : ¬ W₁ ≈ W₂ := Wilkie.not_peq
    contradiction

end MainProof

/-!
# 参考文献

- Joseph Tassarotti. Tarski's High School Algebra Problem. http://www.cs.bc.edu/~tassarot/2011/12/30/Tarski.html
- Stanley Burris, Karen Yeats. The Saga of the High School Identities.
-/
