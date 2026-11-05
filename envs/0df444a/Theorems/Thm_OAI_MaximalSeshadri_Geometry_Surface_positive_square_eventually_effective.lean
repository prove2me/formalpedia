-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_positive_square_eventually_effective
-- name    : OAI.MaximalSeshadri.Geometry.Surface.positive_square_eventually_effective
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:07:28.508935+00:00
-- url     : https://prove2.me/theorems/acba0772-4d6e-44cc-94d2-81aed74d3f55
-- title:
--   Positive square gives effective powers
-- statement:
--   For $L$ ample on $S$ and a line bundle $M$ with $M^2>0$ and $L\cdot M\ge0$, there is $N>0$ such that for all $n\ge N$ the bundle $M^n$ has a nonzero section.
--
--   **Notation.** $L^2$ is `selfIntersection`, namely $\chi(L^2)-2\chi(L)+\chi(\mathcal O_S)$. $L\cdot M$ is `mixedEuler`, namely $\chi(L\otimes M)-\chi(L)-\chi(M)+\chi(\mathcal O_S)$. `IsAmple` means that for each point $x$ and open $V\ni x$, some positive power has a global section with nonvanishing open containing $x$, inside $V$, and affine. A `Surface` is an integral scheme smooth of relative dimension 2 over $\operatorname{Spec}\mathbb C$ with a closed immersion into some complex projective space over $\mathbb C$.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Geometry.Surface.positive_square_eventually_effective`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Intersection/PositiveSquareEffectivity.lean#L18

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective

theorem Surface.positive_square_eventually_effective (S : Surface)
    (L : LineBundle S.scheme) (hL : L.IsAmple) (M : LineBundle S.scheme)
    (hq : 0 < selfIntersection S M) (hm : 0 ≤ mixedEuler S L M) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
      ∃ s : O S.scheme ⟶ (M.pow n).sheaf, s ≠ 0 := by
  sorry

end
end MaximalSeshadri.Geometry
end
end OAI
