-- Prove2me | Theorems.Thm_GlobalTheory_LeviDesc_Krylov_mul_krylov_eq
-- name    : GlobalTheory.LeviDesc.Krylov.mul_krylov_eq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:02:45.016179+00:00
-- url     : https://prove2.me/theorems/048b03d7-e4e9-4386-ac5f-bf94399fdc1b
-- title:
--   Krylov: mul krylov eq
-- statement:
--   The Krylov construction uses the mul krylov eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/KrylovMatrixConjEqOfCharpolyEq.lean#L24-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/KrylovMatrixConjEqOfCharpolyEq.lean#L24-L46

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

theorem GlobalTheory.LeviDesc.Krylov.mul_krylov_eq {F : Type} [Field F] {r : ℕ} (y : Matrix (Fin r) (Fin r) F) (e : Fin r → F) :
    y * krylov y e = krylov y e * companion r y.charpoly := by sorry
