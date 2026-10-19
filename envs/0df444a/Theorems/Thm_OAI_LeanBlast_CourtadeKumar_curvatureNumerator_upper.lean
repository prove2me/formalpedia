-- Prove2me | Theorems.Thm_OAI_LeanBlast_CourtadeKumar_curvatureNumerator_upper
-- name    : OAI.LeanBlast.CourtadeKumar.curvatureNumerator_upper
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T14:57:34.921188+00:00
-- url     : https://prove2.me/theorems/41221ef2-f011-4aa3-a42d-0514e865f543
-- title:
--   A rational upper bound for the curvature numerator
-- statement:
--   For $0<u<1$,
--   $$
--   \frac{(1+u^2)\operatorname{artanh}u-u}{u^3}\le\frac{N(u^2)}{1-u^2},
--   $$
--   where
--   $$
--   N(z)=(1-z)\Bigl(\tfrac43+\tfrac8{15}z+\tfrac{12}{35}z^2+\tfrac{16}{63}z^3+\tfrac{20}{99}z^4\Bigr)+\tfrac{24}{143}z^5 .
--   $$
--
--   The left side is the numerator of the curvature $r''$ of the rate function.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/BooleanNoise/MediumCurvature.lean#L77-L103

import Mathlib
import Definitions.Def_SoftChannel204
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Model
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Statement
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Model
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Basic__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropyScalars__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CurvatureCertificates__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_InverseScalars__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropySeries__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropyBounds__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_MediumCurvature__SoftChannel204

open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open Finset Set
open scoped BigOperators

theorem OAI.LeanBlast.CourtadeKumar.curvatureNumerator_upper {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    (((1 + u ^ 2) * Real.artanh u - u) / u ^ 3) ≤
      curvatureN (u ^ 2) / (1 - u ^ 2) := by sorry
