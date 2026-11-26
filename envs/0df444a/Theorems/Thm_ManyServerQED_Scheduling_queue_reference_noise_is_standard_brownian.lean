-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_queue_reference_noise_is_standard_brownian
-- name    : ManyServerQED.Scheduling.queue_reference_noise_is_standard_brownian
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T03:42:17.903236+00:00
-- url     : https://prove2.me/theorems/8974c8ea-8230-482d-b939-9252b4a096fe
-- title:
--   The normalized reference queue noise is standard Brownian
-- statement:
--   Start with independent standard Brownian drivers for the arrival, service, and abandonment coordinates. The normalized difference of the arrival driver and the service driver evaluated at the fluid clock is again a standard Brownian motion in each coordinate, and the coordinate paths are independent.
-- source:
--   Supporting lemma for Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Definitions.Def_ManyServerQED_Scheduling_Model
import Theorems.Thm_ManyServerQED_Scheduling_independent_brownian_normalized_linear_combination
import Theorems.Thm_ManyServerQED_Scheduling_independent_disjoint_groups_of_primitive_fields
open Filter Topology Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open ManyServerQED.Scheduling

theorem ManyServerQED.Scheduling.queue_reference_noise_is_standard_brownian {Ω Ω' : Type*} [MeasurableSpace Ω] [mΩ' : MeasurableSpace Ω']
    {k : ℕ} (M : SystemSequence Ω k) {P' : Measure Ω'} [IsProbabilityMeasure P']
    (B : Fin (k+k+k) → ℝ≥0 → Ω' → ℝ)
    (hB : ∀ j, IsBrownianReal (B j) P') (hBm : ∀ j t, Measurable (B j t))
    (hI : iIndepFun (fun j ω (t : ℝ≥0) => B j t ω) P') :
    let W (t : ℝ≥0) (ω : Ω') (i : Fin k) :=
      (Real.sqrt (M.lam i*M.cU2 i)*B (Fin.castAdd k (Fin.castAdd k i)) t ω -
        Real.sqrt (M.mu i)*B (Fin.castAdd k (Fin.natAdd k i)) ((M.rho i).toNNReal*t) ω) /
        M.diffData.r i
    (∀ i, IsBrownianReal (fun t ω => W t ω i) P') ∧
      iIndepFun (fun i ω (t : ℝ≥0) => W t ω i) P' := by sorry
