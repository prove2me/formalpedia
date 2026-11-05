-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_cohomology_finite
-- name    : OAI.MaximalSeshadri.Geometry.Surface.cohomology_finite
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:06:30.86518+00:00
-- url     : https://prove2.me/theorems/e7ff0838-4823-4d4a-9fb7-bd25125db703
-- title:
--   Finite cohomology of line bundles on a surface
-- statement:
--   For a surface $S$ with ample $A$, a line bundle $L$ and $n\in\mathbb N$, $\operatorname{Ext}^n(\mathcal O_S,L)$ is finite over $\mathbb C$.
--
--   **Notation.** `IsAmple` means that for each point $x$ and open $V\ni x$, some positive power has a global section with nonvanishing open containing $x$, inside $V$, and affine. A `Surface` is an integral scheme smooth of relative dimension 2 over $\operatorname{Spec}\mathbb C$ with a closed immersion into some complex projective space over $\mathbb C$.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Geometry.Surface.cohomology_finite`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Intersection/SurfaceEuler.lean#L21

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective

theorem Surface.cohomology_finite (S : Surface) (A : LineBundle S.scheme) (hA : A.IsAmple)
    (L : LineBundle S.scheme) (n : ℕ) :
    letI := Module.compHom (cohomology L.sheaf n) (baseScalars S.structureMap)
    Module.Finite ℂ (cohomology L.sheaf n) := by
  sorry

end
end MaximalSeshadri.Geometry
end
end OAI
