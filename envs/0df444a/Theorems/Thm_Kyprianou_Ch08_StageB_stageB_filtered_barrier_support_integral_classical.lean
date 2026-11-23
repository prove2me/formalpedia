-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_stageB_filtered_barrier_support_integral_classical
-- name    : Kyprianou.Ch08.StageB.stageB_filtered_barrier_support_integral_classical
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T03:36:02.207803+00:00
-- url     : https://prove2.me/theorems/4c7134b9-7d3e-4c70-a4d7-5fe33e86665c
-- title:
--   Filtered barrier support integral identity with classical decidability
-- statement:
--   Identifies the real integral of the constant multiple of the rational-barrier supremum with the discounted set integral over the filtered no-drawdown event. The support identity hIS and effective-domain equality hRed are premises, so the helper imports no Open platform theorem. Parent: 47fdba96-7849-46b6-87b0-6cea26c5eadd. Corrected The nonnegative coefficient premise hc was added because ENNReal.ofReal c discards negative values. This corrected theorem replaces the v11 statement with the same name family. Final v13 adds Classical scoped decidability for the if-then-else propositions in the statement.
-- source:
--   Identifies the real integral of the constant multiple of the rational-barrier supremum with the discounted set integral over the filtered no-drawdown event. The support identity hIS and effective-domain equality hRed are premises, so the helper imports no Open platform theorem. Parent: 47fdba96-7849-46b6-87b0-6cea26c5eadd. Corrected The nonnegative coefficient premise hc was added because ENNReal.ofReal c discards negative values. This corrected theorem replaces the v11 statement with the same name family. Final v13 adds Classical scoped decidability for the if-then-else propositions in the statement.

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

theorem Kyprianou.Ch08.StageB.stageB_filtered_barrier_support_integral_classical
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (b h q c : ℝ) (hb : 0 < b) (hh : 0 < h)
    (hc : 0 ≤ c)
    (hE : MeasurableSet {ω : Ω |
      twoSidedExitUpTime X b ω < ⊤ ∧ NoDrawdownBeforeUpcrossing X.X b h ω})
    (hN : NullMeasurableSet {ω : Ω | NoDrawdownBeforeUpcrossing X.X b h ω} P)
    (hIS : ∀ ω : Ω,
      (⨆ r : stageB_Bars h, stageB_bpay X (r : ℝ) b q ω) =
        if twoSidedExitUpTime X b ω < ⊤ ∧ NoDrawdownBeforeUpcrossing X.X b h ω then
          ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X b ω).toReal))) else 0)
    (hRed : (∫ ω in {ω : Ω | NoDrawdownBeforeUpcrossing X.X b h ω},
      c * discountedAt q (tauPlus X.X b ω) ∂P) =
      (∫ ω in {ω : Ω | tauPlus X.X b ω < ⊤ ∧ NoDrawdownBeforeUpcrossing X.X b h ω},
        c * discountedAt q (tauPlus X.X b ω) ∂P)) :
    (∫ ω, (ENNReal.ofReal c *
      (⨆ r : stageB_Bars h, stageB_bpay X (r : ℝ) b q ω)).toReal ∂P) =
    (∫ ω in {ω : Ω | NoDrawdownBeforeUpcrossing X.X b h ω},
      c * discountedAt q (tauPlus X.X b ω) ∂P) := by
  sorry
