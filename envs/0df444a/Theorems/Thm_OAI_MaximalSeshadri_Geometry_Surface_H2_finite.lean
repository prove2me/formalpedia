-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_H2_finite
-- name    : OAI.MaximalSeshadri.Geometry.Surface.H2_finite
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:17:45.289478+00:00
-- url     : https://prove2.me/theorems/d4059e09-434d-4a58-bc52-096d40ffdf16
-- title:
--   Finiteness of H^2 on a surface
-- statement:
--   Let $S$ be a surface with ample $A$. For a line bundle $L$, $\operatorname{Ext}^2(\mathcal O_S,L)$ is a finite $\mathbb C$-module.
--
--   **Notation.** `IsAmple` means that for each point $x$ and open $V\ni x$, some positive power has a global section with nonvanishing open containing $x$, inside $V$, and affine. A `Surface` is an integral scheme smooth of relative dimension 2 over $\operatorname{Spec}\mathbb C$ with a closed immersion into some complex projective space over $\mathbb C$.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Geometry.Surface.H2_finite`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Cohomology/SurfaceH2Finite.lean#L48

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Projective MaximalSeshadri.Frames BaseSections

variable {K : Type} [Field K] {X : Scheme.{0}}

theorem Surface.H2_finite (S : Surface) (A : LineBundle S.scheme) (hA : A.IsAmple)
    (L : LineBundle S.scheme) :
    letI := Module.compHom (cohomology L.sheaf 2) (baseScalars S.structureMap)
    Module.Finite ℂ (cohomology L.sheaf 2) := by
  sorry

end
end MaximalSeshadri.Geometry
end
end OAI
