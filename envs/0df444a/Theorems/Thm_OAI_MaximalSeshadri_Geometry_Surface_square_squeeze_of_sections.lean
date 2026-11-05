-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_square_squeeze_of_sections
-- name    : OAI.MaximalSeshadri.Geometry.Surface.square_squeeze_of_sections
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:06:07.465367+00:00
-- url     : https://prove2.me/theorems/6b1ac9d8-c9e9-4b0e-a205-71a85c165d82
-- title:
--   Squeezing self-intersections from section dimensions
-- statement:
--   Let $S,T$ be surfaces with $L$ ample on $S$, $D$ ample on $T$, and $k,r\in\mathbb N$. If for all $n$ one has $h^0(T,D^n)\le h^0(S,L^{kn})$ and $2h^0(S,L^{kn})\le 2h^0(T,D^n)+rn(n+1)$, then $k^2L^2-r\le D^2\le k^2L^2$.
--
--   **Notation.** $L^2$ is `selfIntersection`, namely $\chi(L^2)-2\chi(L)+\chi(\mathcal O_S)$. $h^n$ is `cohomologyDimension`, the `Module.finrank` over $\mathbb C$ of $\operatorname{Ext}^n(\mathcal O,-)$, which is 0 for an infinite-dimensional space. `IsAmple` means that for each point $x$ and open $V\ni x$, some positive power has a global section with nonvanishing open containing $x$, inside $V$, and affine. A `Surface` is an integral scheme smooth of relative dimension 2 over $\operatorname{Spec}\mathbb C$ with a closed immersion into some complex projective space over $\mathbb C$.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Geometry.Surface.square_squeeze_of_sections`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Blowup/BlowupIntersectionGrowth.lean#L37

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.NefNumerics

theorem Surface.square_squeeze_of_sections (S T : Surface)
    (L : LineBundle S.scheme) (hL : L.IsAmple)
    (D : LineBundle T.scheme) (hD : D.IsAmple) (k r : ℕ)
    (hb : ∀ n : ℕ,
      cohomologyDimension T.structureMap (D.pow n).sheaf 0 ≤ cohomologyDimension S.structureMap (L.pow (k*n)).sheaf 0 ∧
      2*cohomologyDimension S.structureMap (L.pow (k*n)).sheaf 0 ≤
        2*cohomologyDimension T.structureMap (D.pow n).sheaf 0 + r*n*(n+1)) :
    (k:ℤ)^2*selfIntersection S L-r ≤ selfIntersection T D ∧
    selfIntersection T D ≤ (k:ℤ)^2*selfIntersection S L := by
  sorry

end
end MaximalSeshadri.Geometry
end
end OAI
