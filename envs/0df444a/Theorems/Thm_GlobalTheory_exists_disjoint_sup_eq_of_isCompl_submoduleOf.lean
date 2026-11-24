-- Prove2me | Theorems.Thm_GlobalTheory_exists_disjoint_sup_eq_of_isCompl_submoduleOf
-- name    : GlobalTheory.exists_disjoint_sup_eq_of_isCompl_submoduleOf
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:31:11.7528+00:00
-- url     : https://prove2.me/theorems/7add61fc-14fe-4dd5-a863-7f6ba6c3e6cc
-- title:
--   Global Theory: exists disjoint sup eq of is Compl submodule Of
-- statement:
--   The Global Theory construction uses the exists disjoint sup eq of is Compl submodule Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsSaturatedSubmoduleIffExistsIsComplOfValuationR.lean#L32-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsSaturatedSubmoduleIffExistsIsComplOfValuationR.lean#L32-L41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsSaturatedSubmoduleIffExistsIsComplOfValuationR
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory
variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

theorem GlobalTheory.exists_disjoint_sup_eq_of_isCompl_submoduleOf {P N : Submodule R M} (hle : N ≤ P)
    {Q : Submodule R P} (h : IsCompl (N.submoduleOf P) Q) :
    ∃ N' : Submodule R M, Disjoint N N' ∧ N ⊔ N' = P := by sorry
