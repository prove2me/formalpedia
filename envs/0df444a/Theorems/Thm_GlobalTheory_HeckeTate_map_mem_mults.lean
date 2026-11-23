-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTate_map_mem_mults
-- name    : GlobalTheory.HeckeTate.map_mem_mults
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:49:56.896242+00:00
-- url     : https://prove2.me/theorems/3fad4456-e79c-4353-ad5e-b80969b33898
-- title:
--   Hecke Tate: map mem mults
-- statement:
--   The Hecke Tate construction uses the map mem mults property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/DvdMulOfIdem.lean#L149-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/DvdMulOfIdem.lean#L149-L151

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DvdMulOfIdem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HeckeTate
variable {R : Type} [CommRing R] {M M' : Type} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
variable {σ : R ≃+* R} {B : M →+ M →+ ℤ} {B' : M' →+ M' →+ ℤ}

theorem GlobalTheory.HeckeTate.map_mem_mults {N : R} (u : M →ₗ[R] M') {x : M} (hx : x ∈ mults M N) : u x ∈ mults M' N := by sorry
