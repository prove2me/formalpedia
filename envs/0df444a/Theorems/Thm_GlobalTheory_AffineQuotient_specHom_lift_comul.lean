-- Prove2me | Theorems.Thm_GlobalTheory_AffineQuotient_specHom_lift_comul
-- name    : GlobalTheory.AffineQuotient.specHom_lift_comul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:35:47.882217+00:00
-- url     : https://prove2.me/theorems/d23e63ff-3f43-4ef9-971d-396ab2a82b19
-- title:
--   Affine Quotient: spec Hom lift comul
-- statement:
--   The Affine Quotient construction uses the spec Hom lift comul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SpecHomCompCoaction.lean#L45-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SpecHomCompCoaction.lean#L45-L55

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

theorem GlobalTheory.AffineQuotient.specHom_lift_comul {T : Type} [CommRing T] [Algebra R T] (φ ψ : Λ →ₐ[R] T) :
    specHom ((Algebra.TensorProduct.lift φ ψ fun _ _ ↦ .all _ _).comp
      (Bialgebra.comulAlgHom R Λ)) = specHom φ * specHom ψ := by sorry
