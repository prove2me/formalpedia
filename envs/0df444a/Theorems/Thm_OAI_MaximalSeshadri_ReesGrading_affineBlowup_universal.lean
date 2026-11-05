-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_ReesGrading_affineBlowup_universal
-- name    : OAI.MaximalSeshadri.ReesGrading.affineBlowup_universal
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:07:19.250776+00:00
-- url     : https://prove2.me/theorems/56bef956-013c-446f-8b9d-060e03bd260b
-- title:
--   Universal property of the affine blow-up
-- statement:
--   Let $R$ be a commutative ring and $I$ an ideal. If $f:Y\to\operatorname{Spec}R$ pulls the ideal sheaf of $I$ back to an invertible ideal, then there is a unique $h:Y\to\operatorname{Proj}\bigoplus I^n$ (`affineBlowup I`) with $h$ followed by the projection equal to $f$.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.ReesGrading.affineBlowup_universal`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Blowup/LocalEquations.lean#L234

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section
namespace MaximalSeshadri.UnitEndomorphism
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
universe u
variable {X : Scheme.{u}}

variable (g : unit X ⟶ unit X)

end
end MaximalSeshadri.UnitEndomorphism
namespace MaximalSeshadri.InvertibleLocal
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open MaximalSeshadri.Geometry
universe u
variable {X Y Z : Scheme} (I : X.IdealSheafData) (f : Y ⟶ X)
variable (J : LineBundle Y) (ι : J.sheaf ⟶ structureSheaf Y)

variable {I f}

end

noncomputable section
open CategoryTheory AlgebraicGeometry
open MaximalSeshadri.Geometry
variable {X Y : Scheme}

end

noncomputable section
open CategoryTheory AlgebraicGeometry
open MaximalSeshadri.Geometry
variable {X Y Z : Scheme}

end
end MaximalSeshadri.InvertibleLocal

namespace MaximalSeshadri.IdealPullback
noncomputable section
open CategoryTheory AlgebraicGeometry
variable {R : Type} [CommRing R] (I : Ideal R)

end
end MaximalSeshadri.IdealPullback

namespace MaximalSeshadri.ReesGrading
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open MaximalSeshadri.Geometry
open SpecMaps
variable {R : Type} [CommRing R] (I : Ideal R)

theorem affineBlowup_universal {Y : Scheme} (f : Y ⟶ Spec (CommRingCat.of R))
    (hf : InvertiblePullbackIdeal (IdealPullback.specIdeal I) f) :
    ∃! h : Y ⟶ affineBlowup I, h ≫ projection I = f := by
  sorry

end
end MaximalSeshadri.ReesGrading
end
end OAI
