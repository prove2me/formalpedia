-- Prove2me | Theorems.Thm_GlobalTheory_AffineQuotient_coaction_free
-- name    : GlobalTheory.AffineQuotient.coaction_free
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:55:18.323747+00:00
-- url     : https://prove2.me/theorems/cb85c63d-2f87-47fe-8df4-98f0de1d950c
-- title:
--   Affine Quotient: coaction free
-- statement:
--   The Affine Quotient construction uses the coaction free property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SpecHomCompCoaction.lean#L138-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SpecHomCompCoaction.lean#L138-L174

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

theorem GlobalTheory.AffineQuotient.coaction_free [Mono i] [Module.Finite R Λ] :
    Function.Surjective (productMap (includeLeft : B →ₐ[R] B ⊗[R] Λ) ρ) := by sorry
