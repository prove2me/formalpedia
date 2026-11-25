-- Prove2me | Theorems.Thm_GlobalTheory_IsSaturatedIn_exists_disjoint_sup_eq
-- name    : GlobalTheory.IsSaturatedIn.exists_disjoint_sup_eq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:11:01.192899+00:00
-- url     : https://prove2.me/theorems/7ed3e9de-a535-5528-88aa-5aa4765b47a1
-- title:
--   Is Saturated In: exists disjoint sup eq
-- statement:
--   The Is Saturated In construction uses the exists disjoint sup eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsSaturatedSubmoduleIffExistsIsComplOfValuationR.lean#L66-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsSaturatedSubmoduleIffExistsIsComplOfValuationR.lean#L66-L69

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
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {M : Type*} [AddCommGroup M] [Module R M]

theorem GlobalTheory.IsSaturatedIn.exists_disjoint_sup_eq {P N : Submodule R M} [Module.Finite R P]
    (h : IsSaturatedIn P N) : ∃ N' : Submodule R M, Disjoint N N' ∧ N ⊔ N' = P := by sorry
