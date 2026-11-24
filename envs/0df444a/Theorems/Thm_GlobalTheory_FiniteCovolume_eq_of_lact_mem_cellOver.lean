-- Prove2me | Theorems.Thm_GlobalTheory_FiniteCovolume_eq_of_lact_mem_cellOver
-- name    : GlobalTheory.FiniteCovolume.eq_of_lact_mem_cellOver
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T13:30:17.963432+00:00
-- url     : https://prove2.me/theorems/9a04f56c-eab7-4d3f-b8c5-61fb30e152b6
-- title:
--   Finite Covolume: eq of lact mem cell Over
-- statement:
--   The Finite Covolume construction uses the eq of lact mem cell Over property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/FinMuOfFiniteCovolume.lean#L340-L359
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/FinMuOfFiniteCovolume.lean#L340-L359

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

theorem GlobalTheory.FiniteCovolume.eq_of_lact_mem_cellOver {r : ℕ} (X : Data E r) {x0 : Frame X.Ψ r} {FF : Set (V (nd X))}
    (hFF : IsFundSet X x0 FF) {x : Frame X.Ψ r} {δ δ' : GL (Fin r) E} (hδ : δ ∈ X.Γ) (hδ' : δ' ∈ X.Γ)
    (h : lact δ x ∈ cellOver X x0 FF) (h' : lact δ' x ∈ cellOver X x0 FF) : δ = δ' := by sorry
