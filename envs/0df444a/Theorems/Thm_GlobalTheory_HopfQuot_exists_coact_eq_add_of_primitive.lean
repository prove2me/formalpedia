-- Prove2me | Theorems.Thm_GlobalTheory_HopfQuot_exists_coact_eq_add_of_primitive
-- name    : GlobalTheory.HopfQuot.exists_coact_eq_add_of_primitive
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T02:48:35.296356+00:00
-- url     : https://prove2.me/theorems/e60f0191-c4ba-5e0d-9a65-160d0da1899e
-- title:
--   Hopf Quot: exists coact eq add of primitive
-- statement:
--   The Hopf Quot construction uses the exists coact eq add of primitive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsCoactionEqAddOfPrimitive.lean#L71-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsCoactionEqAddOfPrimitive.lean#L71-L124

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RigOfOmegaInjectiveOfEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FiniteFaithfullyFlatKer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCoactionEqAddOfPrimitive
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
open GlobalTheory GlobalTheory.HopfQuot

theorem GlobalTheory.HopfQuot.exists_coact_eq_add_of_primitive : ∀ {R Λ B : Type} [CommRing R] [CommRing Λ] [HopfAlgebra R Λ] [Module.Finite R Λ] [Module.Projective R Λ] [CommRing B] [Algebra R B] (ρ : B →ₐ[R] B ⊗[R] Λ), (∀ a, TensorProduct.assoc R B Λ Λ (ρ.toLinearMap.rTensor Λ (ρ a)) = (Coalgebra.comul (R := R) (A := Λ)).lTensor B (ρ a)) → (∀ a, TensorProduct.rid R B ((Coalgebra.counit (R := R) (A := Λ)).lTensor B (ρ a)) = a) → Function.Surjective (Algebra.TensorProduct.productMap (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] Λ) ρ) → ∀ b : Λ, cobOne R Λ b = 0 → ∃ x : B, ρ x = x ⊗ₜ[R] 1 + 1 ⊗ₜ[R] b := by sorry
