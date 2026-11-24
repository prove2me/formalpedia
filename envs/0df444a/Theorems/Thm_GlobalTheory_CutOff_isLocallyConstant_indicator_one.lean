-- Prove2me | Theorems.Thm_GlobalTheory_CutOff_isLocallyConstant_indicator_one
-- name    : GlobalTheory.CutOff.isLocallyConstant_indicator_one
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:32:23.967846+00:00
-- url     : https://prove2.me/theorems/2f97206e-0c64-4c8a-b792-5f4b3dd97f67
-- title:
--   Cut Off: is Locally Constant indicator one
-- statement:
--   The Cut Off construction uses the is Locally Constant indicator one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsLocallyConstantCutoffClosedEmbedding.lean#L33-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsLocallyConstantCutoffClosedEmbedding.lean#L33-L41

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsLocallyConstantCutoffClosedEmbedding
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.CutOff

theorem GlobalTheory.CutOff.isLocallyConstant_indicator_one {R : Type} [TopologicalSpace R] {U : Set R}
    (hU : IsClopen U) : IsLocallyConstant (U.indicator (fun _ => (1 : ℝ))) := by sorry
