-- Prove2me | Theorems.Thm_GlobalTheory_AffineQuotient_specHom_counit
-- name    : GlobalTheory.AffineQuotient.specHom_counit
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:36:01.861815+00:00
-- url     : https://prove2.me/theorems/526eb350-8130-4db6-9618-fcec5f7c9ad2
-- title:
--   Affine Quotient: spec Hom counit
-- statement:
--   The Affine Quotient construction uses the spec Hom counit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SpecHomCompCoaction.lean#L57-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SpecHomCompCoaction.lean#L57-L63

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

theorem GlobalTheory.AffineQuotient.specHom_counit {T : Type} [CommRing T] [Algebra R T] :
    specHom ((Algebra.ofId R T).comp (Bialgebra.counitAlgHom R Λ)) =
      toUnit _ ≫ η[specOver R Λ] := by sorry
