-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_queue_hjb_moments_from_brownian_growth
-- name    : ManyServerQED.Scheduling.queue_hjb_moments_from_brownian_growth
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T04:43:54.637058+00:00
-- url     : https://prove2.me/theorems/9528592c-36a7-56da-93d6-b25cf96dd56d
-- title:
--   All polynomial moments from the Brownian forcing bound
-- statement:
--   Suppose the limiting queue state is bounded on each horizon by a quadratic polynomial times a drift bound and weighted Brownian suprema. Then at each time it has all integer moments with polynomial time growth, and on every compact interval its state moments admit integrable dominating random variables.
-- source:
--   Supporting lemma for Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Mathlib.Algebra.Order.Chebyshev
import Definitions.Def_ManyServerQED_Scheduling_QueueHJBCompactPath
import Theorems.Thm_ManyServerQED_Scheduling_filtered_brownian_coordinate_supremum_moment
open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy

theorem ManyServerQED.Scheduling.queue_hjb_moments_from_brownian_growth {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} [NeZero k] {P : Measure Ω}
    {Z : ℕ → Ω → ℝ → Fin (k+k+k+2) → ℝ} {s : ℕ → ℕ}
    (d : QueueHJBPathSubseq P Z s) (F : Filtration ℝ≥0 d.mΩ')
    (hW : IsStdFBrownian d.Q F d.noise) (r : Fin k → ℝ) (hr : ∀ i, 0 < r i)
    (a : ℝ) (ha : 0 < a)
    (hGrowth : ∀ T : ℝ≥0, ∀ᵐ ω ∂d.Q, ∀ t ≤ T,
      ENNReal.ofReal (l1norm (d.state t ω)) ≤
        ENNReal.ofReal ((k:ℝ)*(1+a*(T:ℝ))^2) *
          (ENNReal.ofReal ((k:ℝ)*a*(1+(T:ℝ))) +
            ∑ i, ENNReal.ofReal (r i) * (⨆ u : Iic T, ENNReal.ofReal |d.noise u.1 ω i|))) :
    (∀ p : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∃ j : ℕ, ∀ t : ℝ≥0,
      Integrable (fun ω => l1norm (d.state t ω)^p) d.Q ∧
      (∫ ω, l1norm (d.state t ω)^p ∂d.Q) ≤ c*(1+(t:ℝ)^j)) ∧
    (∀ (T : ℝ≥0) (q : ℕ), ∃ V : d.Ω' → ℝ, Integrable V d.Q ∧
      ∀ᵐ ω ∂d.Q, ∀ t ≤ T, l1norm (d.state t ω)^q ≤ V ω) := by sorry
