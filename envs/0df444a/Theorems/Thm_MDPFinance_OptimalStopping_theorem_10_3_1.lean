-- Prove2me | Theorems.Thm_MDPFinance_OptimalStopping_theorem_10_3_1
-- name    : MDPFinance.OptimalStopping.theorem_10_3_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T23:46:17.092608+00:00
-- url     : https://prove2.me/theorems/4492cdfc-8a1a-412b-a887-3e21c9b1c83b
-- title:
--   Theorem 10.3.1 — the house selling problem's explicit threshold
-- statement:
--   **Theorem 10.3.1** (p. 317). In the unbounded horizon house selling problem it is optimal
--   to accept the first offer which exceeds the threshold $x^*$, where $x^*$ is the maximum point of
--   the function
--   $$ x \mapsto \frac{-c\,Q([m,x)) + \int_x^\infty x'Q(dx')}{1 - \beta Q([m,x))} $$
--   on the interval $E = [m,M]$ and $x^* < M$.
--
--   The first fully explicit answer in the chapter: not just "a threshold exists" but a
--   one-dimensional maximisation that produces it. The numerator is the expected reward of one round of
--   the threshold policy — pay $-c$ on each rejection, collect the offer on acceptance — and the
--   denominator discounts the geometric number of rounds.
--
--   $x^* < M$ is a genuine part of the statement, not a boundary remark: it says the seller does not
--   hold out for the maximum possible offer, which is what makes the policy stop almost surely and
--   hence optimal at all, since Corollary 10.2.6 a) is applied to it precisely through
--   $\mathbb{P}_x(\tau^* < \infty) = 1$.
--
--   This is the unbounded-horizon version, so $\beta \in (0,1)$ strictly.
--
--   **Moderation note.** The draft assumed Assumption (B) as a hypothesis although the book derives it (`β < 1`, bounded rewards); dropped. The threshold rule's stopping time is stated to be a stopping time, a.s. finite on `E`, and to attain `V_∞^*` on `E`.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 317 (PDF 325), Theorem 10.3.1

import Mathlib
import Definitions.Def_MDPFinance_OptimalStopping_Applications

open MeasureTheory Filter Topology

namespace MDPFinance.OptimalStopping

/-- **Theorem 10.3.1** (p. 317). In the unbounded-horizon house selling problem it is optimal to
accept the first offer exceeding the threshold `x^*`, a maximum point on `[m,M]` of
`x ↦ (-c Q([m,x)) + ∫_x^∞ x' Q(dx')) / (1 − β Q([m,x)))`, and `x^* < M`. -/
theorem theorem_10_3_1 (H : HouseSelling) (Pr : ℝ → Measure (ℕ → ℝ))
    (hPr : H.toProblem.IsPathLaw Pr) :
    ∃ xstar ∈ H.E,
      IsGreatest (H.thresholdObjective '' H.E) (H.thresholdObjective xstar) ∧
      xstar < H.M ∧
      IsStopTime (hitTime {y : ℝ | xstar ≤ y}) ∧
      (∀ x ∈ H.E, Pr x {w | hitTime {y : ℝ | xstar ≤ y} w = ⊤} = 0) ∧
      ∀ x ∈ H.E, H.toProblem.EReward Pr (hitTime {y : ℝ | xstar ≤ y}) x =
        H.toProblem.Vstar Pr x := by sorry

end MDPFinance.OptimalStopping
