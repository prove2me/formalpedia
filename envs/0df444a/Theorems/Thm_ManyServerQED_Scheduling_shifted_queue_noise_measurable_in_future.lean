-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_shifted_queue_noise_measurable_in_future
-- name    : ManyServerQED.Scheduling.shifted_queue_noise_measurable_in_future
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T04:10:29.851564+00:00
-- url     : https://prove2.me/theorems/f3513df7-aac3-51ef-b76f-6ea52eb8020b
-- title:
--   Measurability of the restarted queue noise
-- statement:
--   At a fixed queue time, consider the centered arrival suffix after the first following arrival and the centered service suffix after the actual busy time, run at fluid scale. Their normalized difference at a fixed nonnegative lag is measurable in both the ambient sigma field and the queue's future information.
-- source:
--   Supporting lemma for Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Theorems.Thm_ManyServerQED_Scheduling_scp_joint_state_measurable
import Definitions.Def_ManyServerQED_Scheduling_Policy
import Theorems.Thm_AvramDividend_Classical_rightContinuous_measurable_sections_joint_evaluation
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy

theorem ManyServerQED.Scheduling.shifted_queue_noise_measurable_in_future {Ω : Type*} [mΩ : MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (hn : 1 ≤ n) (X₀ : Fin k → ℕ)
    (X Ψ : Ω → ℝ → Fin k → ℝ) (hC : M.IsSCP n X₀ X Ψ)
    (i : Fin k) (b u : ℝ≥0) :
    let V (ω : Ω) :=
      ((M.Ahat n ω (M.nextArrival n i ω b+u) i - M.Ahat n ω (M.nextArrival n i ω b) i) -
        (M.Shat n ω (busyTime Ψ ω i b/(n:ℝ)+M.rho i*u) i -
          M.Shat n ω (busyTime Ψ ω i b/(n:ℝ)) i))/M.diffData.r i
    Measurable V ∧ Measurable[M.futureInfo n X Ψ b] V := by sorry
