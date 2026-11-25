-- Prove2me | Theorems.Thm_GlobalTheory_LeadJets_nmat_zero_mem_Bor
-- name    : GlobalTheory.LeadJets.nmat_zero_mem_Bor
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T02:48:05.654734+00:00
-- url     : https://prove2.me/theorems/d8fa7c39-265e-4959-b31e-9199ee56aa95
-- title:
--   Lead Jets: nmat zero mem Bor
-- statement:
--   The Lead Jets construction uses the nmat zero mem Bor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/NmatZeroMemBor.lean#L201-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/NmatZeroMemBor.lean#L201-L206

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_TaylorExpansionLocalCoordinates
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_NmatZeroMemBor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open Filter Asymptotics
open GlobalTheory GlobalTheory.LeadJets
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.LeadJets.nmat_zero_mem_Bor {r : ℕ} (X : Data E r) : nmat X 0 ∈ Bor X.Ψ r := by sorry
