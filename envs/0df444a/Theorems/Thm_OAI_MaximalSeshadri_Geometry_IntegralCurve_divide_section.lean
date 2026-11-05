-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_IntegralCurve_divide_section
-- name    : OAI.MaximalSeshadri.Geometry.IntegralCurve.divide_section
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:07:35.744611+00:00
-- url     : https://prove2.me/theorems/3cad8df9-cb8b-443b-a76c-d586e17d3e49
-- title:
--   Division of a section vanishing on a curve
-- statement:
--   Let $C$ be an integral curve on $S$, $J,\iota$ presenting the ideal of $C$ on $S$ (pullback along the identity), and $s$ a section of a line bundle $M$ whose pullback to $C$ vanishes. Then there is a unique section $q$ of $J\otimes M$ with $q\circ(J\otimes M\to M)=s$.
--
--   **Notation.** `PresentsPullbackIdeal I f J ι` says that $\iota:J\to\mathcal O_Y$ is a monomorphism whose image on affine opens is the extension of $I$ along $f$. A `Surface` is an integral scheme smooth of relative dimension 2 over $\operatorname{Spec}\mathbb C$ with a closed immersion into some complex projective space over $\mathbb C$. An `IntegralCurve` on a surface is an integral closed subscheme of topological Krull dimension one, given by a closed immersion.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Geometry.IntegralCurve.divide_section`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Divisors/CartierResidual.lean#L39

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective MaximalSeshadri.ProjectiveBertini

variable {X Y : Scheme.{0}}

theorem IntegralCurve.divide_section (S : Surface) (C : IntegralCurve S)
    (J M : LineBundle S.scheme) (ι : J.sheaf ⟶ O S.scheme)
    (hJ : PresentsPullbackIdeal C.embedding.ker (𝟙 S.scheme) J ι)
    (s : O S.scheme ⟶ M.sheaf) (hs : pullbackSection C.embedding s = 0) :
    ∃! q : O S.scheme ⟶ (J.tensor M).sheaf, q ≫ tensorInclusion J M ι = s := by
  sorry

end
end MaximalSeshadri.Geometry
end
end OAI
