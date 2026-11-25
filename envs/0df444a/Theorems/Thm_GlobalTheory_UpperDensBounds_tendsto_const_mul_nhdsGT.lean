-- Prove2me | Theorems.Thm_GlobalTheory_UpperDensBounds_tendsto_const_mul_nhdsGT
-- name    : GlobalTheory.UpperDensBounds.tendsto_const_mul_nhdsGT
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:23:22.382157+00:00
-- url     : https://prove2.me/theorems/707e9f87-a251-44be-b2e2-6536bd4893e2
-- title:
--   Upper Dens Bounds: tendsto const mul nhds GT
-- statement:
--   The Upper Dens Bounds construction uses the tendsto const mul nhds GT property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/UpperDensityBoundsAlmostHomogeneousMeasure.lean#L13-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/UpperDensityBoundsAlmostHomogeneousMeasure.lean#L13-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_UpperDens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_UpperDensityBoundsAlmostHomogeneousMeasure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
noncomputable section
open GlobalTheory GlobalTheory.UpperDensBounds
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem GlobalTheory.UpperDensBounds.tendsto_const_mul_nhdsGT {k : ℝ} (hk : 0 < k) :
    Tendsto (fun r : ℝ => k * r) (𝓝[>] 0) (𝓝[>] 0) := by sorry
