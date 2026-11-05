-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_mixedEuler_tensor_right_general
-- name    : OAI.MaximalSeshadri.Geometry.mixedEuler_tensor_right_general
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:07:11.969947+00:00
-- url     : https://prove2.me/theorems/e5986701-fc76-4415-b685-709a8e388022
-- title:
--   Mixed Euler number is additive on the right
-- statement:
--   For a surface with ample $A$ and line bundles $M,N,P$: $M\cdot(N\otimes P)=M\cdot N+M\cdot P$, with $\cdot$ the mixed Euler number.
--
--   **Notation.** $L\cdot M$ is `mixedEuler`, namely $\chi(L\otimes M)-\chi(L)-\chi(M)+\chi(\mathcal O_S)$. `IsAmple` means that for each point $x$ and open $V\ni x$, some positive power has a global section with nonvanishing open containing $x$, inside $V$, and affine. A `Surface` is an integral scheme smooth of relative dimension 2 over $\operatorname{Spec}\mathbb C$ with a closed immersion into some complex projective space over $\mathbb C$.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Geometry.mixedEuler_tensor_right_general`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Intersection/IntersectionBilinear.lean#L33

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames

theorem mixedEuler_tensor_right_general (S : Surface) (A : LineBundle S.scheme) (hA : A.IsAmple)
    (M N P : LineBundle S.scheme) :
    mixedEuler S M (N.tensor P) = mixedEuler S M N + mixedEuler S M P := by
  sorry

end
end MaximalSeshadri.Geometry
end
end OAI
