-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_curveDegree_pow
-- name    : OAI.MaximalSeshadri.Geometry.curveDegree_pow
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:05:46.644912+00:00
-- url     : https://prove2.me/theorems/443c1b8f-08d0-4d06-901f-cbf95a7783ed
-- title:
--   Multiplicativity of the curve degree
-- statement:
--   For a surface $S$ with an ample bundle, a line bundle $L$, an integral curve $C$, and $n\in\mathbb N$: $\deg_C(L^n)=n\deg_CL$.
--
--   **Notation.** $\deg_CL$ is `curveDegree`, namely $\chi(L|_C)-\chi(\mathcal O_C)$. `IsAmple` means that for each point $x$ and open $V\ni x$, some positive power has a global section with nonvanishing open containing $x$, inside $V$, and affine. A `Surface` is an integral scheme smooth of relative dimension 2 over $\operatorname{Spec}\mathbb C$ with a closed immersion into some complex projective space over $\mathbb C$. An `IntegralCurve` on a surface is an integral closed subscheme of topological Krull dimension one, given by a closed immersion.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Geometry.curveDegree_pow`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Intersection/AmbientCurveDegree.lean#L30

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames

theorem curveDegree_pow (S : Surface) (A : LineBundle S.scheme) (hA : A.IsAmple)
    (L : LineBundle S.scheme) (C : IntegralCurve S) (n : ℕ) :
    curveDegree S (L.pow n) C = (n : ℤ) * curveDegree S L C := by
  sorry

end
end MaximalSeshadri.Geometry
end
end OAI
