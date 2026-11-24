-- Prove2me | Theorems.Thm_GlobalTheory_matrix_exists_left_inverse_of_forall_field
-- name    : GlobalTheory.matrix_exists_left_inverse_of_forall_field
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:09:44.417885+00:00
-- url     : https://prove2.me/theorems/fcaaacb9-8e90-4d6f-b955-f09c89a05cb0
-- title:
--   Global Theory: matrix exists left inverse of forall field
-- statement:
--   The Global Theory construction uses the matrix exists left inverse of forall field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsLeftInverseOfFibrewiseInjective.lean#L19-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsLeftInverseOfFibrewiseInjective.lean#L19-L51

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsLeftInverseOfFibrewiseInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.matrix_exists_left_inverse_of_forall_field (R : Type) [CommRing R] (m n : ℕ)
    (Q : Matrix (Fin m) (Fin n) R)
    (h : ∀ (K : Type) [Field K] (φ : R →+* K), Function.Injective (Q.map φ).mulVec) :
    ∃ Q' : Matrix (Fin n) (Fin m) R, Q' * Q = 1 := by sorry
