-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_idempotent_tmul_one_eq_of_smooth_algebra
-- name    : GlobalTheory.T.exists_idempotent_tmul_one_eq_of_smooth_algebra
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T20:35:45.790116+00:00
-- url     : https://prove2.me/theorems/d86893a4-4e2a-45b6-8b4e-f99501e6136d
-- title:
--   T: exists idempotent tmul one eq of smooth algebra
-- statement:
--   The T construction uses the exists idempotent tmul one eq of smooth algebra property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsIdempotentTmulOneEqOfSmoothAlgebraStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsIdempotentTmulOneEqOfSmoothAlgebraStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIdempotentTmulOneEqOfSmoothAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIdempotentTmulOneEqOfSmoothAlgebraStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_idempotent_tmul_one_eq_of_smooth_algebra : ∀ (R A : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CommRing A] [Algebra R A], Algebra.Smooth R A → ∀ ε : A ⊗[R] FractionRing R, IsIdempotentElem ε → ∃ a : A, IsIdempotentElem a ∧ a ⊗ₜ[R] (1 : FractionRing R) = ε := by sorry
