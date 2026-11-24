-- Prove2me | Theorems.Thm_GlobalTheory_LeviDesc_Krylov_krylov_conj_eq_of_charpoly_eq
-- name    : GlobalTheory.LeviDesc.Krylov.krylov_conj_eq_of_charpoly_eq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:02:27.327971+00:00
-- url     : https://prove2.me/theorems/e67aa4f4-1280-4cc4-8360-1a50e87e1963
-- title:
--   Krylov: krylov conj eq of charpoly eq
-- statement:
--   The Krylov construction uses the krylov conj eq of charpoly eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/KrylovMatrixConjEqOfCharpolyEq.lean#L53-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/KrylovMatrixConjEqOfCharpolyEq.lean#L53-L57

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

theorem GlobalTheory.LeviDesc.Krylov.krylov_conj_eq_of_charpoly_eq {F : Type} [Field F] {r : ℕ} (y y' : Matrix (Fin r) (Fin r) F)
    (e e' : Fin r → F) (hχ : y.charpoly = y'.charpoly) (h : IsUnit (krylov y e).det)
    (h' : IsUnit (krylov y' e').det) :
    (krylov y e)⁻¹ * y * krylov y e = (krylov y' e')⁻¹ * y' * krylov y' e' := by sorry
