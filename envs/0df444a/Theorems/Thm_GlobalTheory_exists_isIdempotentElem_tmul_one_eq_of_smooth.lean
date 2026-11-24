-- Prove2me | Theorems.Thm_GlobalTheory_exists_isIdempotentElem_tmul_one_eq_of_smooth
-- name    : GlobalTheory.exists_isIdempotentElem_tmul_one_eq_of_smooth
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:32:52.023257+00:00
-- url     : https://prove2.me/theorems/f154c37d-a658-41fa-9006-e2dfc9455bba
-- title:
--   Global Theory: exists is Idempotent Elem tmul one eq of smooth
-- statement:
--   The Global Theory construction uses the exists is Idempotent Elem tmul one eq of smooth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsIdempotentTmulOneEqOfSmoothAlgebra.lean#L9-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsIdempotentTmulOneEqOfSmoothAlgebra.lean#L9-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIntegralOfIsIdempotentElem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIdempotentTmulOneEqOfSmoothAlgebra
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
open GlobalTheory

theorem GlobalTheory.exists_isIdempotentElem_tmul_one_eq_of_smooth :
    ∀ (R A : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CommRing A] [Algebra R A],
      Algebra.Smooth R A → ∀ ε : A ⊗[R] FractionRing R, IsIdempotentElem ε →
        ∃ a : A, IsIdempotentElem a ∧ a ⊗ₜ[R] (1 : FractionRing R) = ε := by sorry
