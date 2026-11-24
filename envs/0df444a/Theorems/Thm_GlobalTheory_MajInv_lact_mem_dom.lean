-- Prove2me | Theorems.Thm_GlobalTheory_MajInv_lact_mem_dom
-- name    : GlobalTheory.MajInv.lact_mem_dom
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:20:24.959175+00:00
-- url     : https://prove2.me/theorems/933a9f07-bef2-41bb-a2ae-61bfc79980f3
-- title:
--   Maj Inv: lact mem dom
-- statement:
--   The Maj Inv construction uses the lact mem dom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/MajLactRmul.lean#L92-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/MajLactRmul.lean#L92-L105

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantConjugateTransfer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MajLactRmul
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
open GlobalTheory GlobalTheory.MajInv
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.MajInv.lact_mem_dom {r : ℕ} (X : Data E r) {γ : GL (Fin r) E} (hγ : IsUStab X.Gm X.Λ γ)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) : lact γ x ∈ X.dom := by sorry
