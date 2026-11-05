-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_PointBlowup_smooth_rational_point_blowup
-- name    : OAI.MaximalSeshadri.PointBlowup.smooth_rational_point_blowup
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:04:07.931232+00:00
-- url     : https://prove2.me/theorems/5146cc24-9cbd-447d-ae4b-43a4c7ecb089
-- title:
--   Blow-up of a smooth surface at a rational point is smooth
-- statement:
--   Let $K$ be a field, $f:X\to\operatorname{Spec}K$ smooth of relative dimension 2, $p$ a section of $f$, and $\pi:B\to X$ a blow-up of the ideal of $p$. Then $B\to\operatorname{Spec}K$ is smooth of relative dimension 2.
--
--   **Notation.** `IsBlowup I π` says that $I$ pulls back to an invertible ideal along $\pi$ and that $\pi$ is universal with this property.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.PointBlowup.smooth_rational_point_blowup`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Blowup/PointSmoothness.lean#L168

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section
namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
variable {X Y B : Scheme.{0}} {I : X.IdealSheafData} {π : B ⟶ X}

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.IdealPullback
noncomputable section
open AlgebraicGeometry CategoryTheory
variable {R : Type} [CommRing R]

end
end MaximalSeshadri.IdealPullback

namespace MaximalSeshadri.PointBlowup
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MaximalSeshadri.Geometry
variable {K S : Type} [Field K] [CommRing S] [Algebra K S]

end
end MaximalSeshadri.PointBlowup

namespace MaximalSeshadri.IdealPullback
noncomputable section
open AlgebraicGeometry CategoryTheory
variable {R S : Type} [CommRing R] [CommRing S]

end
end MaximalSeshadri.IdealPullback

namespace MaximalSeshadri.PointBlowup
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MaximalSeshadri.Geometry
variable {K : Type} [Field K] {X B : Scheme}

theorem smooth_rational_point_blowup (f : X ⟶ Spec (.of K))
    [SmoothOfRelativeDimension 2 f] (p : Spec (.of K) ⟶ X)
    (hp : p ≫ f = 𝟙 _) (π : B ⟶ X) (hπ : IsBlowup p.ker π) :
    SmoothOfRelativeDimension 2 (π ≫ f) := by
  sorry

end
end MaximalSeshadri.PointBlowup
end
end OAI
