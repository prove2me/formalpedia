-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_IntegralCurve_H1_le
-- name    : OAI.MaximalSeshadri.Geometry.IntegralCurve.H1_le
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:06:59.325102+00:00
-- url     : https://prove2.me/theorems/86bfa697-eac9-457e-92f3-c86519c8fba9
-- title:
--   H^1 comparison on an integral curve
-- statement:
--   Let $C$ be an integral curve on a surface $S$ with an ample $A$, and $M$ a line bundle on $C$ with $\chi(M)-\chi(\mathcal O_C)\ge0$. Then $h^1(C,M)\le h^1(C,\mathcal O_C)$.
--
--   **Notation.** $\chi$ is `eulerCharacteristic`: the alternating sum of $\mathbb C$-dimensions of $\operatorname{Ext}^n(\mathcal O,-)$, for $n\le2$ on a surface and $n\le1$ on a curve. $h^n$ is `cohomologyDimension`, the `Module.finrank` over $\mathbb C$ of $\operatorname{Ext}^n(\mathcal O,-)$, which is 0 for an infinite-dimensional space. `IsAmple` means that for each point $x$ and open $V\ni x$, some positive power has a global section with nonvanishing open containing $x$, inside $V$, and affine. A `Surface` is an integral scheme smooth of relative dimension 2 over $\operatorname{Spec}\mathbb C$ with a closed immersion into some complex projective space over $\mathbb C$. An `IntegralCurve` on a surface is an integral closed subscheme of topological Krull dimension one, given by a closed immersion.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Geometry.IntegralCurve.H1_le`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Cohomology/CurveH1Bound.lean#L57

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective

variable {X : Scheme.{0}} [IsIntegral X] [IsNoetherian X]

theorem IntegralCurve.H1_le (S : Surface) (C : IntegralCurve S)
    (A : LineBundle S.scheme) (hA : A.IsAmple) (M : LineBundle C.scheme)
    (hdeg : 0 ≤ eulerCharacteristic (C.embedding ≫ S.structureMap) 1 M.sheaf -
      eulerCharacteristic (C.embedding ≫ S.structureMap) 1 (O C.scheme)) :
    cohomologyDimension (C.embedding ≫ S.structureMap) M.sheaf 1 ≤
      cohomologyDimension (C.embedding ≫ S.structureMap) (O C.scheme) 1 := by
  sorry

end
end MaximalSeshadri.Geometry
end
end OAI
