-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_IntegralCurve_ample_degree_positive
-- name    : OAI.MaximalSeshadri.Geometry.IntegralCurve.ample_degree_positive
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:05:23.909004+00:00
-- url     : https://prove2.me/theorems/a6f441bb-e3f8-4bb3-b19f-808831f74d3e
-- title:
--   An ample bundle has positive degree on curves
-- statement:
--   For an integral curve $C$ on a surface $S$ and $L$ ample: $\deg_CL>0$.
--
--   **Notation.** $\deg_CL$ is `curveDegree`, namely $\chi(L|_C)-\chi(\mathcal O_C)$. `IsAmple` means that for each point $x$ and open $V\ni x$, some positive power has a global section with nonvanishing open containing $x$, inside $V$, and affine. A `Surface` is an integral scheme smooth of relative dimension 2 over $\operatorname{Spec}\mathbb C$ with a closed immersion into some complex projective space over $\mathbb C$. An `IntegralCurve` on a surface is an integral closed subscheme of topological Krull dimension one, given by a closed immersion.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Geometry.IntegralCurve.ample_degree_positive`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Intersection/SurfacePositiveSquare.lean#L18

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective

theorem IntegralCurve.ample_degree_positive (S : Surface) (C : IntegralCurve S)
    (L : LineBundle S.scheme) (hL : L.IsAmple) : 0 < curveDegree S L C := by
  sorry

end
end MaximalSeshadri.Geometry
end
end OAI
