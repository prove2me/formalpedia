-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_sections_finite
-- name    : OAI.MaximalSeshadri.Geometry.Surface.sections_finite
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:17:48.084907+00:00
-- url     : https://prove2.me/theorems/68aa0933-b002-4a05-b607-daedf3d8058f
-- title:
--   Global sections on a surface are finite-dimensional
-- statement:
--   For $L$ ample on a surface $S$ and any line bundle $M$, the space of global sections of $M$ is a finite-dimensional $\mathbb C$-vector space under `complexSectionModule`.
--
--   **Notation.** `IsAmple` means that for each point $x$ and open $V\ni x$, some positive power has a global section with nonvanishing open containing $x$, inside $V$, and affine. A `Surface` is an integral scheme smooth of relative dimension 2 over $\operatorname{Spec}\mathbb C$ with a closed immersion into some complex projective space over $\mathbb C$.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Geometry.Surface.sections_finite`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Divisors/SectionGermSystem.lean#L72

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory Abelian TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.ProjectiveBertini
open MaximalSeshadri.AnalyticCoordinates MaximalSeshadri.AlgebraicJets
open MaximalSeshadri.ActualInterpolation MaximalSeshadri.LocalComparison

variable {X : Scheme.{0}}

theorem Surface.sections_finite (S : Surface) (L : LineBundle S.scheme) (hL : L.IsAmple)
    (M : LineBundle S.scheme) :
    letI := complexSectionModule S.structureMap M.sheaf
    Module.Finite ℂ (GlobalSections S.scheme M.sheaf) := by
  sorry

end
end MaximalSeshadri.Geometry
end
end OAI
