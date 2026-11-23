-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTate_exists_local_iso
-- name    : GlobalTheory.HeckeTate.exists_local_iso
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:35:59.949802+00:00
-- url     : https://prove2.me/theorems/a4ae83ad-5d1f-4606-8d9a-c2bb5b588ff3
-- title:
--   Hecke Tate: exists local iso
-- statement:
--   The Hecke Tate construction uses the exists local iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUnimodDiv.lean#L8-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUnimodDiv.lean#L8-L42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DvdMulOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUnimodDiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.HeckeTate

theorem GlobalTheory.HeckeTate.exists_local_iso {R : Type} [CommRing R] [IsDedekindDomain R] {M M' : Type} [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] [Module.Finite R M] [Module.Finite R M'] [Module.IsTorsionFree R M]
    [Module.IsTorsionFree R M'] (hr : Module.finrank R M = Module.finrank R M') (P : Ideal R) [P.IsPrime] :
    ∃ (φ : M →ₗ[R] M') (φ' : M' →ₗ[R] M) (s : R), s ∉ P ∧ (∀ a, φ' (φ a) = s • a) ∧ ∀ y, φ (φ' y) = s • y := by sorry
