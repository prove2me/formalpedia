-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_H1_finite
-- name    : OAI.MaximalSeshadri.Geometry.Surface.H1_finite
-- status  : Open
-- author  : @nonlocally
-- created : 2026-11-05T19:06:43.042256+00:00
-- url     : https://prove2.me/theorems/46f45654-15fc-473a-8fcc-f7700d40d892
-- title:
--   Finite $H^1$ of a line bundle on a surface
-- statement:
--   Let $S$ be an integral scheme smooth of relative dimension $2$ over $\mathbb C$ and equipped with a closed immersion into complex projective space. Let $A$ be an ample line bundle on $S$. For every line bundle $L$ on $S$, the degree-$1$ sheaf cohomology $\operatorname{Ext}^1(\mathcal O_S,L)$ is a finite-dimensional $\mathbb C$-module.
--
--   This is the degree-$1 input to the finite-dimensionality theorem for all cohomological degrees.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math; Lean declaration `OAI.MaximalSeshadri.Geometry.Surface.H1_finite`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Cohomology/SurfaceH1Finite.lean#L101-L104

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective

theorem Surface.H1_finite (S : Surface) (A : LineBundle S.scheme) (hA : A.IsAmple)
    (L : LineBundle S.scheme) :
    letI := Module.compHom (cohomology L.sheaf 1) (baseScalars S.structureMap)
    Module.Finite ℂ (cohomology L.sheaf 1) := by
  sorry

end
end MaximalSeshadri.Geometry
end
end OAI
