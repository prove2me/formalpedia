-- Prove2me | Theorems.Thm_MatMulPolyBarrier_Operational_proposition_5_7
-- name    : MatMulPolyBarrier.Operational.proposition_5_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:08:32.751196+00:00
-- url     : https://prove2.me/theorems/7f5e92bb-9e10-460a-a84c-d6c5c5e4d062
-- title:
--   Proposition 5.7 — any preorder under which every $F^\star_\theta$ is monotone obeys the barrier (5.1), and $n^{9/4}\le r$
-- statement:
--   Let $\preceq'$ be any preorder on $\mathcal F$, and let $n_1,n_2,n_3,r\ge1$ be integers with $\langle n_1,n_2,n_3\rangle\preceq'\langle r\rangle$. Logarithms are to base $2$.
--
--   (i) If $F^\star_\theta(T)\le F^\star_\theta(S)$ for all $T,S\in\mathcal F$ with $T\preceq'S$ and for all $\theta\in\Theta$, then, with $a\ge b\ge c$ the numbers $\log n_1,\log n_2,\log n_3$ in nonincreasing order,
--   $$\log r\ \ge\ \begin{cases}a+b & \text{if } c(a+b)\le ab,\\[2pt] \dfrac{(ab+bc+ca)^2}{4abc} & \text{if } c(a+b)>ab.\end{cases}$$
--   (ii) Suppose $n_1=n_2=n_3=n$. If $F^\star_{(1/3,1/3,1/3)}(T)\le F^\star_{(1/3,1/3,1/3)}(S)$ for all $T,S\in\mathcal F$ with $T\preceq'S$, then $r\ge n^{9/4}$.
--
--   The proposition separates the barrier from the specific preorder: any extension of $\preceq$ that keeps the $F^\star_\theta$ monotone obeys the same bound.
--
--   Differences from the source:
--   - encoding: "a preorder ⪯′ on F" → R : FExpr → FExpr → Prop, reflexive on F and transitive on F; the monotonicity hypotheses quantify over T, S ∈ F; reason: values of R outside F are never consulted, so this is the same class of relations
--   - encoding: "a ≥ b ≥ c the numbers log n₁, log n₂, log n₃ in nonincreasing order" → for all reals a, b, c with b ≤ a, c ≤ b and {a, b, c} = {logb 2 n₁, logb 2 n₂, logb 2 n₃} as multisets; reason: this is exactly the sorted triple, for every ordering of ties
--   - encoding: the piecewise bound (5.1) → two implications, c(a+b) ≤ ab → a + b ≤ logb 2 r and ab < c(a+b) → (ab+bc+ca)²/(4abc) ≤ logb 2 r; reason: the two cases are complementary; same content
--   - encoding: log → Real.logb 2; n^{9/4} → (n₁ : ℝ) ^ ((9 : ℝ) / 4) under n₁ = n₂ = n₃; ⟨r⟩, ⟨n₁, n₂, n₃⟩ → unitR r, mm n₁ n₂ n₃; (1/3, 1/3, 1/3) → ![1/3, 1/3, 1/3]; reason: the paper's base-2 convention (p. 4) and the shorthands of the definition file
-- source:
--   Amanov, van den Berg, Zuiddam, Multiplying matrices via polynomials: operational asymptotic spectrum barrier, STOC 2027 submission (manuscript sha256 38bd5183…), p. 39, Proposition 5.7; log convention p. 4 (§1.2)

import Mathlib
import Definitions.Def_MatMulPolyBarrier_Operational_FExpr
import Definitions.Def_MatMulPolyBarrier_Operational_Fstar

set_option autoImplicit false

namespace MatMulPolyBarrier.Operational

/-- Proposition 5.7, p. 39: let `⪯′` be any preorder on `F` (here `R`, reflexive and transitive on
`F`) and `n₁, n₂, n₃, r ≥ 1` integers with `⟨n₁, n₂, n₃⟩ ⪯′ ⟨r⟩`.
(i) If every `F⋆_θ`, `θ ∈ Θ`, is `⪯′`-monotone on `F`, then with `a ≥ b ≥ c` the numbers
`log n₁, log n₂, log n₃` (base 2) in nonincreasing order, `log r ≥ a + b` if `c(a + b) ≤ ab` and
`log r ≥ (ab + bc + ca)²/(4abc)` if `c(a + b) > ab`.
(ii) If `n₁ = n₂ = n₃ = n` and `F⋆_{(1/3,1/3,1/3)}` is `⪯′`-monotone on `F`, then `r ≥ n^{9/4}`. -/
theorem proposition_5_7 (R : FExpr → FExpr → Prop) (hrefl : ∀ T : FExpr, T.WF → R T T)
    (htrans : ∀ T U S : FExpr, T.WF → U.WF → S.WF → R T U → R U S → R T S)
    (n₁ n₂ n₃ r : ℕ) (h₁ : 1 ≤ n₁) (h₂ : 1 ≤ n₂) (h₃ : 1 ≤ n₃) (hr : 1 ≤ r)
    (hR : R (mm n₁ n₂ n₃) (unitR r)) :
    ((∀ θ : Fin 3 → ℝ, InTheta θ →
        ∀ T S : FExpr, T.WF → S.WF → R T S → Fstar θ T ≤ Fstar θ S) →
      ∀ a b c : ℝ, b ≤ a → c ≤ b →
        ({a, b, c} : Multiset ℝ) =
          {Real.logb 2 (n₁ : ℝ), Real.logb 2 (n₂ : ℝ), Real.logb 2 (n₃ : ℝ)} →
        (c * (a + b) ≤ a * b → a + b ≤ Real.logb 2 (r : ℝ)) ∧
        (a * b < c * (a + b) →
          (a * b + b * c + c * a) ^ 2 / (4 * a * b * c) ≤ Real.logb 2 (r : ℝ))) ∧
    (n₁ = n₂ → n₂ = n₃ →
      (∀ T S : FExpr, T.WF → S.WF → R T S →
        Fstar ![1 / 3, 1 / 3, 1 / 3] T ≤ Fstar ![1 / 3, 1 / 3, 1 / 3] S) →
      (n₁ : ℝ) ^ ((9 : ℝ) / 4) ≤ (r : ℝ)) := by sorry

end MatMulPolyBarrier.Operational
