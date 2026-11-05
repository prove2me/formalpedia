-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_IntegralCurve_invertible_ideal
-- name    : OAI.MaximalSeshadri.Geometry.IntegralCurve.invertible_ideal
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:06:46.689203+00:00
-- url     : https://prove2.me/theorems/43bb1711-d95c-48c8-bcf0-23601282b60b
-- title:
--   The ideal of an integral curve is invertible
-- statement:
--   For an integral curve $C$ on a surface $S$, the kernel ideal of $C\to S$ pulled back along the identity is invertible: $C$ is Cartier on $S$.
--
--   **Notation.** A `Surface` is an integral scheme smooth of relative dimension 2 over $\operatorname{Spec}\mathbb C$ with a closed immersion into some complex projective space over $\mathbb C$. An `IntegralCurve` on a surface is an integral closed subscheme of topological Krull dimension one, given by a closed immersion.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Geometry.IntegralCurve.invertible_ideal`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Divisors/IntegralCurveCartier.lean#L107

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section

namespace MaximalSeshadri.LocalCurve
noncomputable section

end
end MaximalSeshadri.LocalCurve

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.ProjectiveBertini

theorem IntegralCurve.invertible_ideal (S : Surface) (C : IntegralCurve S) :
    InvertiblePullbackIdeal C.embedding.ker (𝟙 S.scheme) := by
  sorry

end
end MaximalSeshadri.Geometry
end
end OAI
