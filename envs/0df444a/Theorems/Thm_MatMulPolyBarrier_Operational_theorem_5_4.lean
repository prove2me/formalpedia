-- Prove2me | Theorems.Thm_MatMulPolyBarrier_Operational_theorem_5_4
-- name    : MatMulPolyBarrier.Operational.theorem_5_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:08:35.20965+00:00
-- url     : https://prove2.me/theorems/815282d9-80f4-41a5-9bdc-f44311ab0f8e
-- title:
--   Theorem 5.4 (Operational barrier) — $\langle n_1,n_2,n_3\rangle\preceq\langle r\rangle$ forces $\log r\ge$ (5.1), so $n^{9/4}\le r$
-- statement:
--   **Theorem 5.4 (Operational barrier).** Let $n_1,n_2,n_3,r\ge1$ be integers with $\langle n_1,n_2,n_3\rangle\preceq\langle r\rangle$, where $\preceq$ is the operational preorder of Definition 5.3 on formal expressions, $\langle n_1,n_2,n_3\rangle=P_{n_1,1,n_1}\otimes P_{n_2,n_2,1}\otimes P_{1,n_3,n_3}$ and $\langle r\rangle$ is the direct sum of $r$ copies of $\langle1\rangle=P_{1,1,1}$. Logarithms are to base $2$.
--
--   (i) Let $a\ge b\ge c$ be the numbers $\log n_1,\log n_2,\log n_3$ in nonincreasing order. Then
--   $$\log r\ \ge\ \begin{cases}a+b & \text{if } c(a+b)\le ab,\\[2pt] \dfrac{(ab+bc+ca)^2}{4abc} & \text{if } c(a+b)>ab.\end{cases}\qquad(5.1)$$
--   (ii) In particular, if $n_1=n_2=n_3=n$, then $n^{9/4}\le r$.
--
--   The preorder $\preceq$ encodes exactly the degeneration ingredients, restrictions, isomorphisms and combination rules used to prove $\omega\le 9/4$ and its rectangular analogues; the theorem says that no combination of them can prove a better bound.
--
--   Differences from the source:
--   - encoding: "a ≥ b ≥ c the numbers log n₁, log n₂, log n₃ in nonincreasing order" → for all reals a, b, c with b ≤ a, c ≤ b and {a, b, c} = {logb 2 n₁, logb 2 n₂, logb 2 n₃} as multisets; reason: this is exactly the sorted triple, for every ordering of ties
--   - encoding: the piecewise bound (5.1) → two implications, c(a+b) ≤ ab → a + b ≤ logb 2 r and ab < c(a+b) → (ab+bc+ca)²/(4abc) ≤ logb 2 r; reason: the two cases are complementary; same content
--   - encoding: log → Real.logb 2; "n₁ = n₂ = n₃ = n, then n^{9/4} ≤ r" → n₁ = n₂ → n₂ = n₃ → (n₁ : ℝ) ^ ((9 : ℝ) / 4) ≤ r; ⪯, ⟨r⟩, ⟨n₁, n₂, n₃⟩ → OpLe, unitR r, mm n₁ n₂ n₃ (fixed bracketings); reason: the paper's base-2 convention (p. 4) and the shorthands of the definition files
-- source:
--   Amanov, van den Berg, Zuiddam, Multiplying matrices via polynomials: operational asymptotic spectrum barrier, STOC 2027 submission (manuscript sha256 38bd5183…), p. 37, Theorem 5.4; log convention p. 4 (§1.2)

import Mathlib
import Definitions.Def_MatMulPolyBarrier_Operational_FExpr
import Definitions.Def_MatMulPolyBarrier_Operational_OpPreorder

set_option autoImplicit false

namespace MatMulPolyBarrier.Operational

/-- Theorem 5.4 (Operational barrier), p. 37: let `n₁, n₂, n₃, r ≥ 1` be integers with
`⟨n₁, n₂, n₃⟩ ⪯ ⟨r⟩` (the operational preorder of Definition 5.3).
(i) Let `a ≥ b ≥ c` be the numbers `log n₁, log n₂, log n₃` (base 2) in nonincreasing order. Then
`log r ≥ a + b` if `c(a + b) ≤ ab`, and `log r ≥ (ab + bc + ca)²/(4abc)` if `c(a + b) > ab` (5.1).
(ii) In particular, if `n₁ = n₂ = n₃ = n`, then `n^{9/4} ≤ r`. -/
theorem theorem_5_4 (n₁ n₂ n₃ r : ℕ) (h₁ : 1 ≤ n₁) (h₂ : 1 ≤ n₂) (h₃ : 1 ≤ n₃) (hr : 1 ≤ r)
    (h : OpLe (mm n₁ n₂ n₃) (unitR r)) :
    (∀ a b c : ℝ, b ≤ a → c ≤ b →
        ({a, b, c} : Multiset ℝ) =
          {Real.logb 2 (n₁ : ℝ), Real.logb 2 (n₂ : ℝ), Real.logb 2 (n₃ : ℝ)} →
        (c * (a + b) ≤ a * b → a + b ≤ Real.logb 2 (r : ℝ)) ∧
        (a * b < c * (a + b) →
          (a * b + b * c + c * a) ^ 2 / (4 * a * b * c) ≤ Real.logb 2 (r : ℝ))) ∧
    (n₁ = n₂ → n₂ = n₃ → (n₁ : ℝ) ^ ((9 : ℝ) / 4) ≤ (r : ℝ)) := by sorry

end MatMulPolyBarrier.Operational
