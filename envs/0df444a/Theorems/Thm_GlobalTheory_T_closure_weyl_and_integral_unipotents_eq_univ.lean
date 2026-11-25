-- Prove2me | Theorems.Thm_GlobalTheory_T_closure_weyl_and_integral_unipotents_eq_univ
-- name    : GlobalTheory.T.closure_weyl_and_integral_unipotents_eq_univ
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:27:10.530809+00:00
-- url     : https://prove2.me/theorems/820f6a30-325b-5e6d-9ee7-2113789ba55d
-- title:
--   T: closure weyl and integral unipotents eq univ
-- statement:
--   The T construction uses the closure weyl and integral unipotents eq univ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/Sl2GeneratedWeylUnipotentStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/Sl2GeneratedWeylUnipotentStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_Sl2GeneratedWeylUnipotent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_Sl2GeneratedWeylUnipotentStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.closure_weyl_and_integral_unipotents_eq_univ : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E], Subgroup.closure ({wS F} ∪ {g | ∃ t : F, (∀ y : F, ‖y‖ < 1 → ‖t * y‖ ≤ 1) ∧ g = nS t}) = ⊤ := by sorry
