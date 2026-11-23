-- Prove2me | Theorems.Thm_GlobalTheory_AffineQuotient_isPushout_equalizer
-- name    : GlobalTheory.AffineQuotient.isPushout_equalizer
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:35:59.348253+00:00
-- url     : https://prove2.me/theorems/68349d63-d2bd-40ad-b0d9-4bda3488d2c0
-- title:
--   Affine Quotient: is Pushout equalizer
-- statement:
--   The Affine Quotient construction uses the is Pushout equalizer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SpecHomCompCoaction.lean#L178-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SpecHomCompCoaction.lean#L178-L218

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
omit hρ

theorem GlobalTheory.AffineQuotient.isPushout_equalizer {T : Type} [CommRing T] [Algebra R T] (α β : B →ₐ[R] T)
    (h₁ : Function.Surjective (productMap β α))
    (h₂ : RingHom.ker (productMap β α) = Ideal.span {z | ∃ b ∈ AlgHom.equalizer α β,
      z = b ⊗ₜ[R] (1 : B) - (1 : B) ⊗ₜ[R] b}) :
    IsPushout (CommRingCat.ofHom (α.toRingHom.eqLocus β.toRingHom).subtype)
      (CommRingCat.ofHom (α.toRingHom.eqLocus β.toRingHom).subtype)
      (CommRingCat.ofHom α.toRingHom) (CommRingCat.ofHom β.toRingHom) := by sorry
