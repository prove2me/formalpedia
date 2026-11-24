-- Prove2me | Theorems.Thm_GlobalTheory_LeviDesc_Krylov_pow_dim_eq_neg_sum_charpoly_coeff
-- name    : GlobalTheory.LeviDesc.Krylov.pow_dim_eq_neg_sum_charpoly_coeff
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:02:38.740797+00:00
-- url     : https://prove2.me/theorems/0fdd302f-fa49-4a21-965d-33bc53752393
-- title:
--   Krylov: pow dim eq neg sum charpoly coeff
-- statement:
--   The Krylov construction uses the pow dim eq neg sum charpoly coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/KrylovMatrixConjEqOfCharpolyEq.lean#L9-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/KrylovMatrixConjEqOfCharpolyEq.lean#L9-L19

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

theorem GlobalTheory.LeviDesc.Krylov.pow_dim_eq_neg_sum_charpoly_coeff {F : Type} [Field F] {r : ℕ} (y : Matrix (Fin r) (Fin r) F) :
    y ^ r = - ∑ k : Fin r, y.charpoly.coeff k • y ^ (k : ℕ) := by sorry
