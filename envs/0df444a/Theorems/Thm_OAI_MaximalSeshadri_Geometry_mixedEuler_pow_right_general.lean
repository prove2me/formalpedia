-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_mixedEuler_pow_right_general
-- name    : OAI.MaximalSeshadri.Geometry.mixedEuler_pow_right_general
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:06:55.541508+00:00
-- url     : https://prove2.me/theorems/4a65384c-6473-4236-9054-664857cc57c3
-- title:
--   Mixed Euler number with a power on the right
-- statement:
--   For a surface with ample $A$, line bundles $M,N$, and $n$: $M\cdot N^n=n\,(M\cdot N)$.
--
--   **Notation.** $L\cdot M$ is `mixedEuler`, namely $\chi(L\otimes M)-\chi(L)-\chi(M)+\chi(\mathcal O_S)$. `IsAmple` means that for each point $x$ and open $V\ni x$, some positive power has a global section with nonvanishing open containing $x$, inside $V$, and affine. A `Surface` is an integral scheme smooth of relative dimension 2 over $\operatorname{Spec}\mathbb C$ with a closed immersion into some complex projective space over $\mathbb C$.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Geometry.mixedEuler_pow_right_general`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Intersection/IntersectionBilinear.lean#L42

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames

theorem mixedEuler_pow_right_general (S : Surface) (A : LineBundle S.scheme) (hA : A.IsAmple)
    (M N : LineBundle S.scheme) (n : ℕ) :
    mixedEuler S M (N.pow n) = (n : ℤ)*mixedEuler S M N := by
  sorry

end
end MaximalSeshadri.Geometry
end
end OAI
