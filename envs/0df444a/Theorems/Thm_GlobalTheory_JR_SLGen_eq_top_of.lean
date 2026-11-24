-- Prove2me | Theorems.Thm_GlobalTheory_JR_SLGen_eq_top_of
-- name    : GlobalTheory.JR.SLGen.eq_top_of
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T17:37:00.334798+00:00
-- url     : https://prove2.me/theorems/13a73606-8b8d-4352-91e1-182aa7ade1eb
-- title:
--   SLGen: eq top of
-- statement:
--   The SLGen construction uses the eq top of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/Sl2GeneratedWeylUnipotent.lean#L59-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/Sl2GeneratedWeylUnipotent.lean#L59-L82

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_Sl2GeneratedWeylUnipotent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.SLGen
variable {F : Type} [Field F]

theorem GlobalTheory.JR.SLGen.eq_top_of (H : Subgroup (SpecialLinearGroup (Fin 2) F)) (hw : wS F ∈ H) (hn : ∀ t, nS t ∈ H) :
    H = ⊤ := by sorry
