-- Prove2me | Theorems.Thm_NestedSeatAlloc_ProbCond_lemma2_cond_right_deriv
-- name    : NestedSeatAlloc.ProbCond.lemma2_cond_right_deriv
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T15:59:20.190869+00:00
-- url     : https://prove2.me/theorems/18c74c2f-833d-408d-9a95-85c2905340c9
-- title:
--   Lemma 2, p. 134 — under (31), δ₊E[R_{k+1}[s; p; X] | X_{k+1}] = f₁Pr[X₁ > p₁ ∩ … ∩ X₁+…+X_k > p_k ∩ X₁+…+X_{k+1} > s | X_{k+1}] for s ≥ p_k
-- statement:
--   Work in the seat model: independent nonnegative demands $X_1, X_2, \dots$ on a probability space, strictly decreasing fares $f_1 > f_2 > \cdots$, and a protection-level policy $p$ with $p_k \ge 0$. Suppose that $p$ satisfies (31):
--   $$f_1 \Pr[X_1 > p_1 \cap X_1 + X_2 > p_2 \cap \dots \cap X_1 + \dots + X_k > p_k] = f_{k+1} \qquad \text{for all } k \ge 1.$$
--   Then for every $k \ge 1$, every value $y \ge 0$ of $X_{k+1}$ and every $s \ge p_k$, the right derivative in $s$ of $E\{R_{k+1}[s; p; X] \mid X_{k+1} = y\}$ exists and equals
--   $$\delta_+ E\{R_{k+1}[s; p; X] \mid X_{k+1} = y\} = f_1 \Pr[X_1 > p_1 \cap \dots \cap X_1 + \dots + X_k > p_k \cap X_1 + \dots + X_k + y > s]. \tag{32}$$
--
--   The lemma expresses the marginal value of a seat in terms of the joint distribution of the cumulative demands, which is what turns the subdifferential conditions (20) into the explicit equations (31).
--
--   **Formalization Note** The page's conditional probability $\Pr[\,\cdots \cap X_1 + \dots + X_{k+1} > s \mid X_{k+1}]$ at $X_{k+1} = y$ is, by independence of the demands, the unconditional probability with $X_{k+1}$ replaced by $y$, which is how the right-hand side is written. "With probability 1" is replaced by "for every $y \ge 0$", which is stronger. The hypothesis (31) is assumed for all $k$, as on the page.
-- source:
--   Brumelle & McGill (1993), Operations Research 41(1), Lemma 2, (31)–(32), p. 134

import Mathlib
import Definitions.Def_NestedSeatAlloc_ProbCond_Model

namespace NestedSeatAlloc.ProbCond

open MeasureTheory ProbabilityTheory

/-- Lemma 2, p. 134: if `p` satisfies (31) for all `k`, then for `k = 1, 2, …`, every value `y ≥ 0` of
`X_{k+1}` and every `s ≥ p_k`, the right derivative in `s` of `E{R_{k+1}[s; p; X] | X_{k+1} = y}` is
`f₁ Pr[X₁ > p₁ ∩ ⋯ ∩ X₁ + ⋯ + X_k > p_k ∩ X₁ + ⋯ + X_k + y > s]` (32). -/
theorem lemma2_cond_right_deriv {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ) (hM : IsSeatModel P X f) (hp : IsProtectionPolicy p)
    (h31 : ProbCondition P X f p) :
    ∀ k, 1 ≤ k → ∀ y, 0 ≤ y → ∀ s, p k ≤ s →
      HasDerivWithinAt (condRevenue P X f p (k + 1) y)
        (f 1 * P.real (nestEvent X p k ∩ {ω | s < (∑ i ∈ Finset.Icc 1 k, X i ω) + y}))
        (Set.Ici s) s := by sorry

end NestedSeatAlloc.ProbCond
