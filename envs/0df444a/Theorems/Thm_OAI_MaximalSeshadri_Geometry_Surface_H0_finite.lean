-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_H0_finite
-- name    : OAI.MaximalSeshadri.Geometry.Surface.H0_finite
-- status  : Open
-- author  : @nonlocally
-- created : 2026-11-05T19:06:47.447171+00:00
-- url     : https://prove2.me/theorems/06d2853e-7240-4b81-a1ef-b80156f973ef
-- title:
--   Finite $H^0$ of a line bundle on a surface
-- statement:
--   Let $S$ be an integral scheme smooth of relative dimension $2$ over $\mathbb C$ and equipped with a closed immersion into complex projective space. Let $A$ be an ample line bundle on $S$. For every line bundle $L$ on $S$, the degree-$0$ sheaf cohomology $\operatorname{Ext}^0(\mathcal O_S,L)$ is a finite-dimensional $\mathbb C$-module.
--
--   This is the degree-$0 input to the finite-dimensionality theorem for all cohomological degrees.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math; Lean declaration `OAI.MaximalSeshadri.Geometry.Surface.H0_finite`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Cohomology/SurfaceH0Finite.lean#L56-L59

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective

theorem Surface.H0_finite (S : Surface) (A : LineBundle S.scheme) (hA : A.IsAmple)
    (L : LineBundle S.scheme) :
    letI := Module.compHom (cohomology L.sheaf 0) (baseScalars S.structureMap)
    Module.Finite ℂ (cohomology L.sheaf 0) := by
  sorry

end
end MaximalSeshadri.Geometry
end
end OAI
