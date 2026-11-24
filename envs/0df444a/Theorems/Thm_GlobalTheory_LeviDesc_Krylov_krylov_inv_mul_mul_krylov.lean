-- Prove2me | Theorems.Thm_GlobalTheory_LeviDesc_Krylov_krylov_inv_mul_mul_krylov
-- name    : GlobalTheory.LeviDesc.Krylov.krylov_inv_mul_mul_krylov
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:02:25.683927+00:00
-- url     : https://prove2.me/theorems/ce3e2b87-1398-4de0-8598-2c3a3cde6481
-- title:
--   Krylov: krylov inv mul mul krylov
-- statement:
--   The Krylov construction uses the krylov inv mul mul krylov property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/KrylovMatrixConjEqOfCharpolyEq.lean#L48-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/KrylovMatrixConjEqOfCharpolyEq.lean#L48-L51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KrylovApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KrylovMatrixConjEqOfCharpolyEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
noncomputable section
open GlobalTheory GlobalTheory.LeviDesc GlobalTheory.LeviDesc.Krylov

theorem GlobalTheory.LeviDesc.Krylov.krylov_inv_mul_mul_krylov {F : Type} [Field F] {r : ℕ} (y : Matrix (Fin r) (Fin r) F)
    (e : Fin r → F) (h : IsUnit (krylov y e).det) :
    (krylov y e)⁻¹ * y * krylov y e = companion r y.charpoly := by sorry
