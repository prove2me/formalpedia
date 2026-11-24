-- Prove2me | Theorems.Thm_GlobalTheory_FiniteCovolume_measurableSet_Bor
-- name    : GlobalTheory.FiniteCovolume.measurableSet_Bor
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T13:30:38.428947+00:00
-- url     : https://prove2.me/theorems/34b6c161-293b-4af4-bf3d-c14478e1132c
-- title:
--   Finite Covolume: measurable Set Bor
-- statement:
--   The Finite Covolume construction uses the measurable Set Bor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/FinMuOfFiniteCovolume.lean#L99-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/FinMuOfFiniteCovolume.lean#L99-L114

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
omit [NumberField E] [IsCMField E]

theorem GlobalTheory.FiniteCovolume.measurableSet_Bor {r : ℕ} (Ψ : Finset (E →+* ℂ)) : MeasurableSet (Bor Ψ r) := by sorry
