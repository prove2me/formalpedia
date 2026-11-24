-- Prove2me | Theorems.Thm_GlobalTheory_UnRep_SmallMat_exists_dvd_pow_mul_coprime
-- name    : GlobalTheory.UnRep.SmallMat.exists_dvd_pow_mul_coprime
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:23:15.570537+00:00
-- url     : https://prove2.me/theorems/88423baa-aada-43f8-84b5-7d8572371784
-- title:
--   Small Mat: exists dvd pow mul coprime
-- statement:
--   The Small Mat construction uses the exists dvd pow mul coprime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IdempotentAdelesAndSmallAdelicMatrices.lean#L13-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IdempotentAdelesAndSmallAdelicMatrices.lean#L13-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteAdeleStrongApproximationModNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeRationalVectorsInAdelicTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdempotentAdelesAndSmallAdelicMatrices
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
open GlobalTheory GlobalTheory.UnRep GlobalTheory.UnRep.SmallMat
open GlobalTheory.AdLat.Translate

theorem GlobalTheory.UnRep.SmallMat.exists_dvd_pow_mul_coprime (N m : ℕ) (hm : m ≠ 0) :
    ∃ t k : ℕ, t.Coprime N ∧ m ∣ N ^ k * t := by sorry
