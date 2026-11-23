-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTate_IsUnimod_smul_cancel
-- name    : GlobalTheory.HeckeTate.IsUnimod.smul_cancel
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:50:05.698936+00:00
-- url     : https://prove2.me/theorems/c5907372-cd35-4369-a5e7-3e02e062cd40
-- title:
--   Is Unimod: smul cancel
-- statement:
--   The Is Unimod construction uses the smul cancel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/DvdMulOfIdem.lean#L143-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/DvdMulOfIdem.lean#L143-L147

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

theorem GlobalTheory.HeckeTate.IsUnimod.smul_cancel (h : IsUnimod σ B) {n : ℕ} (hn : n ≠ 0) {x y : M}
    (e : (n : R) • x = (n : R) • y) : x = y := by sorry
