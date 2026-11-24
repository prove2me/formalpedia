-- Prove2me | Theorems.Thm_GlobalTheory_CutOff_exists_isClopen_isCompact_superset
-- name    : GlobalTheory.CutOff.exists_isClopen_isCompact_superset
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:33:08.624485+00:00
-- url     : https://prove2.me/theorems/d980c282-ce6d-4c43-9202-5b15f2f82f37
-- title:
--   Cut Off: exists is Clopen is Compact superset
-- statement:
--   The Cut Off construction uses the exists is Clopen is Compact superset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsLocallyConstantCutoffClosedEmbedding.lean#L6-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsLocallyConstantCutoffClosedEmbedding.lean#L6-L18

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

theorem GlobalTheory.CutOff.exists_isClopen_isCompact_superset {R : Type} [TopologicalSpace R] [LocallyCompactSpace R]
    [T2Space R] [TotallyDisconnectedSpace R] {Z : Set R} (hZ : IsCompact Z) :
    ∃ U : Set R, IsClopen U ∧ IsCompact U ∧ Z ⊆ U := by sorry
