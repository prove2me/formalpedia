-- Prove2me | Theorems.Thm_NestedSeatAlloc_ProbCond_corollary2_right_deriv
-- name    : NestedSeatAlloc.ProbCond.corollary2_right_deriv
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T15:59:31.935389+00:00
-- url     : https://prove2.me/theorems/341cef5e-f1c5-4b4b-9c9a-7e558beb3ea9
-- title:
--   Corollary 2, p. 134 — under (31), δ₊ER_{k+1}[s; p; X] = f₁Pr[X₁ > p₁ ∩ … ∩ X₁+…+X_k > p_k ∩ X₁+…+X_{k+1} > s] for s ≥ p_k
-- statement:
--   Work in the seat model: independent nonnegative demands $X_1, X_2, \dots$ on a probability space, strictly decreasing fares $f_1 > f_2 > \cdots$, and a protection-level policy $p$ with $p_k \ge 0$. If $p$ satisfies (31),
--   $$f_1 \Pr[X_1 > p_1 \cap \dots \cap X_1 + \dots + X_k > p_k] = f_{k+1} \qquad \text{for all } k \ge 1,$$
--   then for every $k \ge 1$ and every $s \ge p_k$ the right derivative of the expected revenue exists and equals
--   $$\delta_+ ER_{k+1}[s; p; X] = f_1 \Pr[X_1 > p_1 \cap \dots \cap X_1 + \dots + X_k > p_k \cap X_1 + \dots + X_{k+1} > s]. \tag{37}$$
--
--   The corollary gives the marginal expected revenue of a seat for the $k+1$ highest classes in closed form, in terms of the joint distribution of the cumulative demands, under the policy defined by (31).
--
--   **Formalization Note** The page obtains (37) from (32) by taking the expectation over $X_{k+1}$, which uses the independence carried by the seat model.
-- source:
--   Brumelle & McGill (1993), Operations Research 41(1), Corollary 2, (37), p. 134

import Mathlib
import Definitions.Def_NestedSeatAlloc_ProbCond_Model

namespace NestedSeatAlloc.ProbCond

open MeasureTheory ProbabilityTheory

/-- Corollary 2, p. 134: if `p` satisfies (31), then for `k ≥ 1` and `s ≥ p_k` the right derivative of
`ER_{k+1}[s; p; X]` is `f₁ Pr[X₁ > p₁ ∩ ⋯ ∩ X₁ + ⋯ + X_k > p_k ∩ X₁ + ⋯ + X_{k+1} > s]` (37). -/
theorem corollary2_right_deriv {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ) (hM : IsSeatModel P X f) (hp : IsProtectionPolicy p)
    (h31 : ProbCondition P X f p) :
    ∀ k, 1 ≤ k → ∀ s, p k ≤ s →
      HasDerivWithinAt (expRevenue P X f p (k + 1))
        (f 1 * P.real (nestEvent X p k ∩ {ω | s < ∑ i ∈ Finset.Icc 1 (k + 1), X i ω}))
        (Set.Ici s) s := by sorry

end NestedSeatAlloc.ProbCond
