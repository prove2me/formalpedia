-- Prove2me | Theorems.Thm_GlobalTheory_HopfQuot_finite_faithfullyFlat_ker
-- name    : GlobalTheory.HopfQuot.finite_faithfullyFlat_ker
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:36:13.271808+00:00
-- url     : https://prove2.me/theorems/ce04ebc8-6c63-47b1-ac0c-402bb3974ff0
-- title:
--   Hopf Quot: finite faithfully Flat ker
-- statement:
--   The Hopf Quot construction uses the finite faithfully Flat ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FiniteFaithfullyFlatKer.lean#L290-L362
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FiniteFaithfullyFlatKer.lean#L290-L362

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FiniteFaithfullyFlatKer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HopfQuot
open TensorProduct
variable {R Λ B : Type*} [CommRing R] [CommRing Λ] [HopfAlgebra R Λ] [CommRing B] [Algebra R B]
  (ρ : B →ₐ[R] B ⊗[R] Λ)

theorem GlobalTheory.HopfQuot.finite_faithfullyFlat_ker [Module.Finite R Λ] [Module.Projective R Λ]
    (hassoc : ∀ b, TensorProduct.assoc R B Λ Λ (ρ.toLinearMap.rTensor Λ (ρ b)) =
      (Coalgebra.comul (R := R) (A := Λ)).lTensor B (ρ b))
    (hcounit : ∀ b, TensorProduct.rid R B
      ((Coalgebra.counit (R := R) (A := Λ)).lTensor B (ρ b)) = b)
    (hsurj : Function.Surjective (Algebra.TensorProduct.productMap
      (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] Λ) ρ)) :
    Module.Finite (AlgHom.equalizer ρ
      (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] Λ)) B ∧
    Module.Projective (AlgHom.equalizer ρ
      (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] Λ)) B ∧
    Module.FaithfullyFlat (AlgHom.equalizer ρ
      (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] Λ)) B ∧
    RingHom.ker (Algebra.TensorProduct.productMap
        (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] Λ) ρ) =
      Ideal.span {z | ∃ b ∈ AlgHom.equalizer ρ
        (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] Λ),
        z = b ⊗ₜ[R] (1 : B) - (1 : B) ⊗ₜ[R] b} := by sorry
