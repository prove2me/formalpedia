-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_power_H2_bounded
-- name    : OAI.MaximalSeshadri.Geometry.Surface.power_H2_bounded
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:07:40.680396+00:00
-- url     : https://prove2.me/theorems/f57ca404-6dbe-4ab8-ade2-162a6eb76dac
-- title:
--   Bounded H^2 of powers of an ample bundle
-- statement:
--   For $L$ ample on a surface $S$ there is $B$ with $h^2(S,L^n)\le B$ for all $n$.
--
--   **Notation.** $h^n$ is `cohomologyDimension`, the `Module.finrank` over $\mathbb C$ of $\operatorname{Ext}^n(\mathcal O,-)$, which is 0 for an infinite-dimensional space. `IsAmple` means that for each point $x$ and open $V\ni x$, some positive power has a global section with nonvanishing open containing $x$, inside $V$, and affine. A `Surface` is an integral scheme smooth of relative dimension 2 over $\operatorname{Spec}\mathbb C$ with a closed immersion into some complex projective space over $\mathbb C$.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Geometry.Surface.power_H2_bounded`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Geometry/SurfaceTopGrowth.lean#L73

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective

variable {X : Scheme.{0}}

theorem Surface.power_H2_bounded (S : Surface) (L : LineBundle S.scheme) (hL : L.IsAmple) :
    ∃ B : ℕ, ∀ n : ℕ, cohomologyDimension S.structureMap (L.pow n).sheaf 2 ≤ B := by
  sorry

end
end MaximalSeshadri.Geometry
end
end OAI
