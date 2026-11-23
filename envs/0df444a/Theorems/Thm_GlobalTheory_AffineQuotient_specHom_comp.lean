-- Prove2me | Theorems.Thm_GlobalTheory_AffineQuotient_specHom_comp
-- name    : GlobalTheory.AffineQuotient.specHom_comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:35:47.238653+00:00
-- url     : https://prove2.me/theorems/bd589220-7711-4675-a89b-a670806fcafd
-- title:
--   Affine Quotient: spec Hom comp
-- statement:
--   The Affine Quotient construction uses the spec Hom comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SpecHomCompCoaction.lean#L29-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SpecHomCompCoaction.lean#L29-L33

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
variable {S T T' : Type} [CommRing S] [CommRing T] [CommRing T'] [Algebra R S] [Algebra R T]
  [Algebra R T']

theorem GlobalTheory.AffineQuotient.specHom_comp (φ : S →ₐ[R] T) (ψ : T →ₐ[R] T') :
    specHom (ψ.comp φ) = specHom ψ ≫ specHom φ := by sorry
