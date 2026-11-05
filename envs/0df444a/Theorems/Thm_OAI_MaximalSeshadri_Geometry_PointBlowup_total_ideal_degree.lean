-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_PointBlowup_total_ideal_degree
-- name    : OAI.MaximalSeshadri.Geometry.PointBlowup.total_ideal_degree
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:07:52.060495+00:00
-- url     : https://prove2.me/theorems/154dcbbd-3a36-478d-bfde-226dee7b5751
-- title:
--   Degree of the total exceptional ideal
-- statement:
--   Let $B$ be a point blow-up with an ample bundle on its surface, $J,\iota$ presenting the pullback of the centre ideal, and $C$ an integral curve on the blow-up. Then $\deg_CJ=\sum_i\deg_CE_i$.
--
--   **Notation.** $\deg_CL$ is `curveDegree`, namely $\chi(L|_C)-\chi(\mathcal O_C)$. `PresentsPullbackIdeal I f J ι` says that $\iota:J\to\mathcal O_Y$ is a monomorphism whose image on affine opens is the extension of $I$ along $f$. `IsAmple` means that for each point $x$ and open $V\ni x$, some positive power has a global section with nonvanishing open containing $x$, inside $V$, and affine. A `Surface` is an integral scheme smooth of relative dimension 2 over $\operatorname{Spec}\mathbb C$ with a closed immersion into some complex projective space over $\mathbb C$. An `IntegralCurve` on a surface is an integral closed subscheme of topological Krull dimension one, given by a closed immersion. `Configuration S r` is the set of $r$-tuples of complex points with distinct images, with the Zariski topology induced from the product.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Geometry.PointBlowup.total_ideal_degree`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Intersection/IdealProductDegree.lean#L176

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Frames

variable {X : Scheme.{0}}

theorem PointBlowup.total_ideal_degree (S : Surface) {r : ℕ} {p : Configuration S r}
    (B : PointBlowup S r p) (A : LineBundle B.surface.scheme) (hA : A.IsAmple)
    (J : LineBundle B.surface.scheme) (ι : J.sheaf ⟶ O B.surface.scheme)
    (hJ : PresentsPullbackIdeal (centreIdeal S r p) B.projection J ι)
    (C : IntegralCurve B.surface) :
    curveDegree B.surface J C = ∑ i,curveDegree B.surface (B.exceptionalIdeal i) C := by
  sorry

end
end MaximalSeshadri.Geometry
end
end OAI
