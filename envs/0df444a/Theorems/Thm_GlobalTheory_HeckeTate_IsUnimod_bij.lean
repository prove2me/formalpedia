-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTate_IsUnimod_bij
-- name    : GlobalTheory.HeckeTate.IsUnimod.bij
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:44:07.581522+00:00
-- url     : https://prove2.me/theorems/ac70c7f0-b0e5-46fc-ac0b-ceaf9420ec1b
-- title:
--   Is Unimod: bij
-- statement:
--   The Is Unimod construction uses the bij property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/DvdMulOfIdem.lean#L128-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/DvdMulOfIdem.lean#L128-L128

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

theorem GlobalTheory.HeckeTate.IsUnimod.bij (h : IsUnimod σ B) : Function.Bijective B := by sorry
