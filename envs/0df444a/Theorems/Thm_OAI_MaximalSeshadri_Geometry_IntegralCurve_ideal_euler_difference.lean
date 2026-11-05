-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_IntegralCurve_ideal_euler_difference
-- name    : OAI.MaximalSeshadri.Geometry.IntegralCurve.ideal_euler_difference
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:17:45.707432+00:00
-- url     : https://prove2.me/theorems/8dc05bf6-4699-47ce-8ec7-77b27a5499b0
-- title:
--   Euler difference for the ideal of a curve
-- statement:
--   Let $S$ be a surface with ample $A$, $C$ an integral curve, $J,\iota$ presenting the ideal of $C$, and $M$ a line bundle. Then $\chi(M)-\chi(J\otimes M)=\chi(C,M|_C)$.
--
--   **Notation.** $\chi$ is `eulerCharacteristic`: the alternating sum of $\mathbb C$-dimensions of $\operatorname{Ext}^n(\mathcal O,-)$, for $n\le2$ on a surface and $n\le1$ on a curve. `PresentsPullbackIdeal I f J ι` says that $\iota:J\to\mathcal O_Y$ is a monomorphism whose image on affine opens is the extension of $I$ along $f$. `IsAmple` means that for each point $x$ and open $V\ni x$, some positive power has a global section with nonvanishing open containing $x$, inside $V$, and affine. A `Surface` is an integral scheme smooth of relative dimension 2 over $\operatorname{Spec}\mathbb C$ with a closed immersion into some complex projective space over $\mathbb C$. An `IntegralCurve` on a surface is an integral closed subscheme of topological Krull dimension one, given by a closed immersion.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Geometry.IntegralCurve.ideal_euler_difference`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Intersection/CurveIdealDegree.lean#L21

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective

theorem IntegralCurve.ideal_euler_difference (S : Surface)
    (A : LineBundle S.scheme) (hA : A.IsAmple) (C : IntegralCurve S)
    (J : LineBundle S.scheme) (ι : J.sheaf ⟶ O S.scheme)
    (h : PresentsPullbackIdeal C.embedding.ker (𝟙 S.scheme) J ι)
    (M : LineBundle S.scheme) :
    eulerCharacteristic S.structureMap 2 M.sheaf -
      eulerCharacteristic S.structureMap 2 (J.tensor M).sheaf =
      eulerCharacteristic (C.embedding ≫ S.structureMap) 1
        ((Scheme.Modules.pullback C.embedding).obj M.sheaf) := by
  sorry

end
end MaximalSeshadri.Geometry
end
end OAI
