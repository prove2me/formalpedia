-- Prove2me | Theorems.Thm_GlobalTheory_AffineQuotient_coaction_counit
-- name    : GlobalTheory.AffineQuotient.coaction_counit
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:55:10.590857+00:00
-- url     : https://prove2.me/theorems/4da27de7-e4df-4911-8374-071d901d9eb2
-- title:
--   Affine Quotient: coaction counit
-- statement:
--   The Affine Quotient construction uses the coaction counit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SpecHomCompCoaction.lean#L77-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SpecHomCompCoaction.lean#L77-L90

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SpecHomCompCoaction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open TensorProduct Algebra.TensorProduct
open GlobalTheory GlobalTheory.AffineQuotient
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R]
variable {Λ B : Type} [CommRing Λ] [HopfAlgebra R Λ] [CommRing B] [Algebra R B]
variable {A : Over (Spec (CommRingCat.of R))} [GrpObj A]
  (i : specOver R Λ ⟶ A) (v : specOver R B ⟶ A) (ρ : B →ₐ[R] B ⊗[R] Λ)
  (hρ : specHom ρ ≫ v = (specHom includeRight ≫ i) * (specHom includeLeft ≫ v))
include hρ

theorem GlobalTheory.AffineQuotient.coaction_counit [IsMonHom i] [Mono v] (b : B) :
    TensorProduct.rid R B ((Coalgebra.counit (R := R) (A := Λ)).lTensor B (ρ b)) = b := by sorry
