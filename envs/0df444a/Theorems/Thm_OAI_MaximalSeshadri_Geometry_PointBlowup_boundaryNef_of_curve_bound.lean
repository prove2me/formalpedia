-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_PointBlowup_boundaryNef_of_curve_bound
-- name    : OAI.MaximalSeshadri.Geometry.PointBlowup.boundaryNef_of_curve_bound
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:05:41.289333+00:00
-- url     : https://prove2.me/theorems/e59b5793-46c4-404f-a2cc-563962152015
-- title:
--   Boundary nefness from the curve bound
-- statement:
--   Let $L$ be ample on a surface $S$, $r>0$, $p$ a configuration of $r$ points, $B$ a point blow-up, and suppose $\sqrt{L^2/r}\cdot\operatorname{mult}_p(C)\le\deg_CL$ for all integral curves $C$ on $S$. Then $B$ is boundary nef for $L$ in the sense of `PointBlowup.BoundaryNef`: for all integral curves $C$ on the blow-up, $\deg_C(\pi^*L)+\sqrt{L^2/r}\sum_i\deg_C(E_i)\ge0$.
--
--   **Notation.** $L^2$ is `selfIntersection`, namely $\chi(L^2)-2\chi(L)+\chi(\mathcal O_S)$. $\deg_CL$ is `curveDegree`, namely $\chi(L|_C)-\chi(\mathcal O_C)$. $\operatorname{mult}_p(C)$ is `totalMultiplicity`, the sum over the points of `curveMultiplicity`, the order of the kernel ideal of the local ring map of $C$ at the point. `IsAmple` means that for each point $x$ and open $V\ni x$, some positive power has a global section with nonvanishing open containing $x$, inside $V$, and affine. A `Surface` is an integral scheme smooth of relative dimension 2 over $\operatorname{Spec}\mathbb C$ with a closed immersion into some complex projective space over $\mathbb C$. An `IntegralCurve` on a surface is an integral closed subscheme of topological Krull dimension one, given by a closed immersion. `Configuration S r` is the set of $r$-tuples of complex points with distinct images, with the Zariski topology induced from the product.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Geometry.PointBlowup.boundaryNef_of_curve_bound`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Blowup/BoundaryNef.lean#L20

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.NefNumerics

theorem PointBlowup.boundaryNef_of_curve_bound (S : Surface) (L : LineBundle S.scheme)
    (hL : L.IsAmple) {r : ℕ} (hr : 0 < r) {p : Configuration S r}
    (B : PointBlowup S r p)
    (hC : ∀ C : IntegralCurve S,
      Real.sqrt ((selfIntersection S L:ℝ)/r)*(totalMultiplicity S r C p:ℝ) ≤
        (curveDegree S L C:ℝ)) : B.BoundaryNef L := by
  sorry

end
end MaximalSeshadri.Geometry
end
end OAI
