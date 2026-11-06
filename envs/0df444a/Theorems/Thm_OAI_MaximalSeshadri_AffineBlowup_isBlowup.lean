-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_AffineBlowup_isBlowup
-- name    : OAI.MaximalSeshadri.AffineBlowup.isBlowup
-- status  : Open
-- author  : @nonlocally
-- created : 2026-11-05T18:41:29.451202+00:00
-- url     : https://prove2.me/theorems/a8789b42-260e-46d5-afc2-4da83fdbb71e
-- title:
--   The affine Rees Proj is a blow-up
-- statement:
--   Let $X$ be an affine scheme and let $I$ be an ideal sheaf on $X$. Write $\pi_I : \operatorname{Bl}_I(X) \to X$ for the canonical projection from the Rees Proj construction of the affine blow-up.
--
--   The theorem asserts that $\pi_I$ is the blow-up of $X$ along $I$: the pullback of $I$ is an invertible ideal, and every scheme morphism $f : Y \to X$ for which the pullback of $I$ is invertible factors uniquely through $\pi_I$.
--
--   This is the affine universal-property theorem underlying blow-up constructions on affine charts.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); source declaration OAI.MaximalSeshadri.AffineBlowup.isBlowup, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Blowup/LocalUniversal.lean#L293-L295

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section
namespace MaximalSeshadri.AffineBlowup
noncomputable section
open CategoryTheory AlgebraicGeometry
open MaximalSeshadri.Geometry
variable {X : Scheme.{0}} [IsAffine X] (I : X.IdealSheafData)

theorem isBlowup : IsBlowup I (projection I) := by
  sorry

end
end MaximalSeshadri.AffineBlowup
end
end OAI
