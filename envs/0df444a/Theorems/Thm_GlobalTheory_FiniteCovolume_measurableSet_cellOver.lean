-- Prove2me | Theorems.Thm_GlobalTheory_FiniteCovolume_measurableSet_cellOver
-- name    : GlobalTheory.FiniteCovolume.measurableSet_cellOver
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T13:30:43.501367+00:00
-- url     : https://prove2.me/theorems/83ac1dc1-7861-4a93-987d-bab6711cac59
-- title:
--   Finite Covolume: measurable Set cell Over
-- statement:
--   The Finite Covolume construction uses the measurable Set cell Over property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/FinMuOfFiniteCovolume.lean#L282-L297
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/FinMuOfFiniteCovolume.lean#L282-L297

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_FinMuOfFiniteCovolume
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
open GlobalTheory GlobalTheory.FiniteCovolume
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.FiniteCovolume.measurableSet_cellOver {r : ℕ} (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0)
    {FF : Set (V (nd X))} (hm : MeasurableSet FF) (hO : FF ⊆ OmF X x0) :
    MeasurableSet (cellOver X x0 FF) := by sorry
