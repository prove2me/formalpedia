-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_selfIntersection_twist_pow
-- name    : OAI.MaximalSeshadri.Geometry.Surface.selfIntersection_twist_pow
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:06:42.547356+00:00
-- url     : https://prove2.me/theorems/b7e00c12-ba12-455d-824a-077f13f406cc
-- title:
--   Self-intersection of a twist of powers
-- statement:
--   For $L$ ample on $S$, a line bundle $J$, and $a,b\in\mathbb N$: $(L^a\otimes J^b)^2=a^2L^2+2ab\,(L\cdot J)+b^2J^2$, with $L\cdot J$ the mixed Euler number.
--
--   **Notation.** $L^2$ is `selfIntersection`, namely $\chi(L^2)-2\chi(L)+\chi(\mathcal O_S)$. $L\cdot M$ is `mixedEuler`, namely $\chi(L\otimes M)-\chi(L)-\chi(M)+\chi(\mathcal O_S)$. `IsAmple` means that for each point $x$ and open $V\ni x$, some positive power has a global section with nonvanishing open containing $x$, inside $V$, and affine. A `Surface` is an integral scheme smooth of relative dimension 2 over $\operatorname{Spec}\mathbb C$ with a closed immersion into some complex projective space over $\mathbb C$.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Geometry.Surface.selfIntersection_twist_pow`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Intersection/BivariateSurfaceEuler.lean#L75

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames

theorem Surface.selfIntersection_twist_pow (S : Surface)
    (L : LineBundle S.scheme) (hL : L.IsAmple) (J : LineBundle S.scheme) (a b : ℕ) :
    selfIntersection S ((L.pow a).tensor (J.pow b)) =
      (a : ℤ)^2*selfIntersection S L + 2*(a : ℤ)*(b : ℤ)*mixedEuler S L J +
        (b : ℤ)^2*selfIntersection S J := by
  sorry

end
end MaximalSeshadri.Geometry
end
end OAI
