-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTate_IsUnimod_skew
-- name    : GlobalTheory.HeckeTate.IsUnimod.skew
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:43:52.917826+00:00
-- url     : https://prove2.me/theorems/68579f2a-cf9a-4b92-a199-f6f1cfe4a63f
-- title:
--   Is Unimod: skew
-- statement:
--   The Is Unimod construction uses the skew property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/DvdMulOfIdem.lean#L124-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/DvdMulOfIdem.lean#L124-L124

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

theorem GlobalTheory.HeckeTate.IsUnimod.skew (h : IsUnimod σ B) (x y : M) : B x y = -B y x := by sorry
