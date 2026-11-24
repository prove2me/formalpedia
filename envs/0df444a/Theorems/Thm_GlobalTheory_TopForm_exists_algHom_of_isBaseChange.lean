-- Prove2me | Theorems.Thm_GlobalTheory_TopForm_exists_algHom_of_isBaseChange
-- name    : GlobalTheory.TopForm.exists_algHom_of_isBaseChange
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:09:16.335832+00:00
-- url     : https://prove2.me/theorems/3adaaa3f-5db6-4abc-adbf-e18763c0b0bb
-- title:
--   Top Form: exists alg Hom of is Base Change
-- statement:
--   The Top Form construction uses the exists alg Hom of is Base Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExistsAlgHomOfIsBaseChange.lean#L28-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExistsAlgHomOfIsBaseChange.lean#L28-L56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExistsAlgHomOfIsBaseChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open GlobalTheory
open GlobalTheory.TopForm
variable {A B M N : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]

theorem GlobalTheory.TopForm.exists_algHom_of_isBaseChange {φ : M →ₗ[A] N} (hφ : IsBaseChange B φ) :
    ∃ F : ExteriorAlgebra B N →ₐ[B] B ⊗[A] ExteriorAlgebra A M,
      ∀ m, F (ExteriorAlgebra.ι B (φ m)) = 1 ⊗ₜ ExteriorAlgebra.ι A m := by sorry
