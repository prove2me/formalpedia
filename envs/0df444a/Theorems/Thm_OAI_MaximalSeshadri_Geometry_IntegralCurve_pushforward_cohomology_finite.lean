-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_IntegralCurve_pushforward_cohomology_finite
-- name    : OAI.MaximalSeshadri.Geometry.IntegralCurve.pushforward_cohomology_finite
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:17:54.450658+00:00
-- url     : https://prove2.me/theorems/99f26189-aa18-4285-9c54-907afed9d255
-- title:
--   Finite cohomology of pushforwards from a curve
-- statement:
--   For an integral curve $C$ on a surface with ample $A$ and a line bundle $L$ on $C$: $\operatorname{Ext}^n(\mathcal O_S,C_*L)$ is finite over $\mathbb C$ for all $n$.
--
--   **Notation.** `IsAmple` means that for each point $x$ and open $V\ni x$, some positive power has a global section with nonvanishing open containing $x$, inside $V$, and affine. A `Surface` is an integral scheme smooth of relative dimension 2 over $\operatorname{Spec}\mathbb C$ with a closed immersion into some complex projective space over $\mathbb C$. An `IntegralCurve` on a surface is an integral closed subscheme of topological Krull dimension one, given by a closed immersion.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Geometry.IntegralCurve.pushforward_cohomology_finite`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Intersection/SurfaceEuler.lean#L65

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective

theorem IntegralCurve.pushforward_cohomology_finite (S : Surface) (C : IntegralCurve S)
    (A : LineBundle S.scheme) (hA : A.IsAmple) (L : LineBundle C.scheme) (n : ℕ) :
    letI := Module.compHom (cohomology ((Scheme.Modules.pushforward C.embedding).obj L.sheaf) n)
      (baseScalars S.structureMap)
    Module.Finite ℂ (cohomology ((Scheme.Modules.pushforward C.embedding).obj L.sheaf) n) := by
  sorry

end
end MaximalSeshadri.Geometry
end
end OAI
