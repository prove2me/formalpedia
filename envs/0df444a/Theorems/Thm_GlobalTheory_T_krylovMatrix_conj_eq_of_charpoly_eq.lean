-- Prove2me | Theorems.Thm_GlobalTheory_T_krylovMatrix_conj_eq_of_charpoly_eq
-- name    : GlobalTheory.T.krylovMatrix_conj_eq_of_charpoly_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:50:59.524064+00:00
-- url     : https://prove2.me/theorems/0385b7fb-861a-4874-bf3e-d1383f980cb7
-- title:
--   T: krylov Matrix conj eq of charpoly eq
-- statement:
--   The T construction uses the krylov Matrix conj eq of charpoly eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/KrylovMatrixConjEqOfCharpolyEqStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/KrylovMatrixConjEqOfCharpolyEqStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KrylovMatrixConjEqOfCharpolyEq
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KrylovApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KrylovMatrixConjEqOfCharpolyEqStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.krylovMatrix_conj_eq_of_charpoly_eq : ∀ {F : Type} [Field F] {r : ℕ} (y y' : Matrix (Fin r) (Fin r) F) (e e' : Fin r → F), y.charpoly = y'.charpoly → IsUnit (GlobalTheory.LeviDesc.Krylov.krylov y e).det → IsUnit (GlobalTheory.LeviDesc.Krylov.krylov y' e').det → (GlobalTheory.LeviDesc.Krylov.krylov y e)⁻¹ * y * GlobalTheory.LeviDesc.Krylov.krylov y e = (GlobalTheory.LeviDesc.Krylov.krylov y' e')⁻¹ * y' * GlobalTheory.LeviDesc.Krylov.krylov y' e' := by sorry
