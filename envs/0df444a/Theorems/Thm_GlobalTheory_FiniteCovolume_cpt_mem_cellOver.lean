-- Prove2me | Theorems.Thm_GlobalTheory_FiniteCovolume_cpt_mem_cellOver
-- name    : GlobalTheory.FiniteCovolume.cpt_mem_cellOver
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T13:30:09.270746+00:00
-- url     : https://prove2.me/theorems/34d1656c-e83a-4a56-a2f6-60908284ed74
-- title:
--   Finite Covolume: cpt mem cell Over
-- statement:
--   The Finite Covolume construction uses the cpt mem cell Over property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/FinMuOfFiniteCovolume.lean#L315-L324
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/FinMuOfFiniteCovolume.lean#L315-L324

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

theorem GlobalTheory.FiniteCovolume.cpt_mem_cellOver {r : ℕ} (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0)
    {FF : Set (V (nd X))} {z : V (nd X)} : cpt X x0 z ∈ cellOver X x0 FF ↔ z ∈ FF := by sorry
