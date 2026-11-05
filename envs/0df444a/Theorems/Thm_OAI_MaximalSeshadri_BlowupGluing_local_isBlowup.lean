-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_BlowupGluing_local_isBlowup
-- name    : OAI.MaximalSeshadri.BlowupGluing.local_isBlowup
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:06:55.608248+00:00
-- url     : https://prove2.me/theorems/e63c6e21-d73c-44eb-8290-9cd864d5a7e4
-- title:
--   The local Rees Proj is a blow-up
-- statement:
--   For a scheme $X$, an ideal sheaf $I$ and an affine open $U$, the Rees $\operatorname{Proj}$ chart with `localProjection I U` is a blow-up of `localCentre I U`.
--
--   **Notation.** `IsBlowup I π` says that $I$ pulls back to an invertible ideal along $\pi$ and that $\pi$ is universal with this property.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.BlowupGluing.local_isBlowup`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Blowup/Gluing.lean#L28

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section
namespace MaximalSeshadri.BlowupGluing
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MaximalSeshadri.Geometry

variable {X : Scheme.{0}} (I : X.IdealSheafData)

attribute [local instance] OAI.MaximalSeshadri.BlowupGluing.localAffine

theorem local_isBlowup (U : X.AffineZariskiSite) :
    IsBlowup (localCentre I U) (localProjection I U) := by
  sorry

end
end MaximalSeshadri.BlowupGluing
end
end OAI
