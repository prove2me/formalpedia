-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_left_inverse_of_fibrewise_injective
-- name    : GlobalTheory.T.exists_left_inverse_of_fibrewise_injective
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:30:12.973084+00:00
-- url     : https://prove2.me/theorems/15ce3191-1c4c-4ba4-be3e-108d377755ad
-- title:
--   T: exists left inverse of fibrewise injective
-- statement:
--   The T construction uses the exists left inverse of fibrewise injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsLeftInverseOfFibrewiseInjectiveStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsLeftInverseOfFibrewiseInjectiveStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsLeftInverseOfFibrewiseInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsLeftInverseOfFibrewiseInjectiveStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_left_inverse_of_fibrewise_injective : ∀ (R : Type) [CommRing R] (m n : ℕ) (Q : Matrix (Fin m) (Fin n) R), (∀ (K : Type) [Field K] (φ : R →+* K), Function.Injective (Q.map φ).mulVec) → ∃ Q' : Matrix (Fin n) (Fin m) R, Q' * Q = 1 := by sorry
