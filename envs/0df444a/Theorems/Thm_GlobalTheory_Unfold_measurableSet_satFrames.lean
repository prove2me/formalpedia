-- Prove2me | Theorems.Thm_GlobalTheory_Unfold_measurableSet_satFrames
-- name    : GlobalTheory.Unfold.measurableSet_satFrames
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:12:33.99262+00:00
-- url     : https://prove2.me/theorems/b4cc8dcf-421a-4dee-accd-0b5e62cd25dd
-- title:
--   Unfold: measurable Set sat Frames
-- statement:
--   The Unfold construction uses the measurable Set sat Frames property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/MeasurableSetSatFrames.lean#L48-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/MeasurableSetSatFrames.lean#L48-L67

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MeasurableSetSatFrames
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.Unfold
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem GlobalTheory.Unfold.measurableSet_satFrames (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0)
    {A : Set (V (nd X))} (hA : MeasurableSet A) (hAO : A ⊆ OmF X x0) :
    MeasurableSet (satFrames X x0 A) := by sorry
