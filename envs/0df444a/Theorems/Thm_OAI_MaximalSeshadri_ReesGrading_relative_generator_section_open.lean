-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_ReesGrading_relative_generator_section_open
-- name    : OAI.MaximalSeshadri.ReesGrading.relative_generator_section_open
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:10:09.694031+00:00
-- url     : https://prove2.me/theorems/106eeb4d-5bd4-4012-b7fd-62f6375f412d
-- title:
--   Section opens as basic opens of the Rees Proj
-- statement:
--   Let $I$ be an ideal of a ring $R$, $f:B\to\operatorname{Spec}R$, $J,\iota$ presenting the pullback of $I$ along $f$, $\beta:B\to\operatorname{Proj}\bigoplus I^n$ a lift of $f$, and $a\in I$. If a section $s$ of $J$ satisfies $s\circ\iota=$ multiplication by the image of $a$, then the iso-open of $s$ is the preimage under $\beta$ of the basic open of the degree-one generator attached to $a$.
--
--   **Notation.** The iso-open of $s$ (`SectionOpens.isoOpen s`) is the union of the opens on which the morphism $s$ restricts to an isomorphism.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.ReesGrading.relative_generator_section_open`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Blowup/RelativeReesSections.lean#L56

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section

namespace MaximalSeshadri.ReesGrading
noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open MaximalSeshadri.Geometry MaximalSeshadri.Frames MaximalSeshadri.SpecMaps

variable {R : Type} [CommRing R] (I : Ideal R)
variable {B : Scheme.{0}} (f : B ⟶ Spec (.of R))
  (J : LineBundle B) (ι : J.sheaf ⟶ O B)
  (hJ : PresentsPullbackIdeal (IdealPullback.specIdeal I) f J ι)
include hJ

theorem relative_generator_section_open (β : B ⟶ affineBlowup I) (hβ : β ≫ projection I = f) (a : I)
    (s : O B ⟶ J.sheaf)
    (hs : s ≫ ι = scalarEnd ((coordinate f) a.val)) :
    SectionOpens.isoOpen s = β ⁻¹ᵁ Proj.basicOpen (piece I) (generator I a) := by
  sorry

end
end MaximalSeshadri.ReesGrading
end
end OAI
