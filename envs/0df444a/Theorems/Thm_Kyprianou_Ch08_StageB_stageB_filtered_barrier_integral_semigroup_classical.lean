-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_stageB_filtered_barrier_integral_semigroup_classical
-- name    : Kyprianou.Ch08.StageB.stageB_filtered_barrier_integral_semigroup_classical
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T03:36:02.958888+00:00
-- url     : https://prove2.me/theorems/c9a93cf2-054f-43d1-81e4-af0435dcddcd
-- title:
--   Filtered barrier integral semigroup with classical decidability
-- statement:
--   Barrier-algebra decomposition for the parent semigroup. It proves measurability, directedness, the lintegral/iSup interchange, the supremum multiplication identity from the accepted barrier semigroup, and the ENNReal.toReal conversion. The pointwise payoff support identity hIS is supplied as a premise, so the helper imports no Open platform theorem. Parent: 47fdba96-7849-46b6-87b0-6cea26c5eadd. Corrected Nonnegative coefficient premises were added because ENNReal.ofReal discards negative values. This corrected theorem replaces the v11 statement with the same name family. Final v13 adds Classical scoped decidability for the if-then-else propositions in the statement.
-- source:
--   Barrier-algebra decomposition for the parent semigroup. It proves measurability, directedness, the lintegral/iSup interchange, the supremum multiplication identity from the accepted barrier semigroup, and the ENNReal.toReal conversion. The pointwise payoff support identity hIS is supplied as a premise, so the helper imports no Open platform theorem. Parent: 47fdba96-7849-46b6-87b0-6cea26c5eadd. Corrected Nonnegative coefficient premises were added because ENNReal.ofReal discards negative values. This corrected theorem replaces the v11 statement with the same name family. Final v13 adds Classical scoped decidability for the if-then-else propositions in the statement.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_stageB_Bars
import Definitions.Def_stageB_bpay
import Theorems.Thm_stageB_actual_height_barrier_semigroup
import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_mono_barrier
import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_measurable
import Theorems.Thm_AvramDividend_Classical_upperPassage_measurable_from_stopping
import Theorems.Thm_stageB_tauPlus_coe_eq
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open AvramDividend.Classical
open scoped Classical NNReal ENNReal

theorem Kyprianou.Ch08.StageB.stageB_filtered_barrier_integral_semigroup_classical
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (a1 a2 h q c1 c2 c12 : ℝ) (ha1 : 0 < a1) (ha2 : 0 < a2) (hh : 0 < h)
    (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) (hc12 : 0 ≤ c12)
    (hmul : c12 = c1 * c2)
    (hIS : ∀ (b : ℝ) (hb : 0 < b) (ω : Ω),
      (⨆ r : stageB_Bars h, stageB_bpay X (r : ℝ) b q ω) =
        if twoSidedExitUpTime X b ω < ⊤ ∧ NoDrawdownBeforeUpcrossing X.X b h ω then
          ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X b ω).toReal))) else 0) :
    (∫ ω, (ENNReal.ofReal c12 *
      (⨆ r : stageB_Bars h, stageB_bpay X (r : ℝ) (a1 + a2) q ω)).toReal ∂P) =
    (∫ ω, (ENNReal.ofReal c1 *
      (⨆ r : stageB_Bars h, stageB_bpay X (r : ℝ) a1 q ω)).toReal ∂P) *
    (∫ ω, (ENNReal.ofReal c2 *
      (⨆ r : stageB_Bars h, stageB_bpay X (r : ℝ) a2 q ω)).toReal ∂P) := by
  sorry
