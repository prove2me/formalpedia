-- Prove2me | Theorems.Thm_GlobalTheory_JR_sl2_closure_weyl_unipotent_eq_top
-- name    : GlobalTheory.JR.sl2_closure_weyl_unipotent_eq_top
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T17:40:37.009884+00:00
-- url     : https://prove2.me/theorems/188f47ba-cab1-4f2c-b588-bf07a1175fb3
-- title:
--   JR: sl2 closure weyl unipotent eq top
-- statement:
--   The JR construction uses the sl2 closure weyl unipotent eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/Sl2GeneratedWeylUnipotent.lean#L88-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/Sl2GeneratedWeylUnipotent.lean#L88-L128

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
open GlobalTheory.JR.SLGen

theorem GlobalTheory.JR.sl2_closure_weyl_unipotent_eq_top :
    ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
      [Unram F E], Subgroup.closure ({wS F} ∪ {g | ∃ t : F, (∀ y : F, ‖y‖ < 1 → ‖t * y‖ ≤ 1) ∧ g = nS t}) = ⊤ := by sorry
