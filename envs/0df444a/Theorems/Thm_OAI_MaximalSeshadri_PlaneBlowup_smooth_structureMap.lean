-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_PlaneBlowup_smooth_structureMap
-- name    : OAI.MaximalSeshadri.PlaneBlowup.smooth_structureMap
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:07:36.095402+00:00
-- url     : https://prove2.me/theorems/c9f2a358-efa7-4f71-8216-bf86d838390c
-- title:
--   The blow-up of the plane at the origin is smooth
-- statement:
--   For a field $K$, the blow-up of the affine plane over $K$ at the origin is smooth of relative dimension 2 over $K$: `structureMap K` is `SmoothOfRelativeDimension 2`.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.PlaneBlowup.smooth_structureMap`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Blowup/PlaneCharts.lean#L173

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section
namespace MaximalSeshadri.PlaneBlowup
noncomputable section
open MvPolynomial ReesGrading
variable (K : Type) [Field K]

end

noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial ReesGrading
variable (K : Type) [Field K]

theorem smooth_structureMap : SmoothOfRelativeDimension 2 (structureMap K) := by
  sorry

end
end MaximalSeshadri.PlaneBlowup
end
end OAI
