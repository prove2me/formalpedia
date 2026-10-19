-- Prove2me | Theorems.Thm_OAI_LeanBlast_CourtadeKumar_large_curvature_bound
-- name    : OAI.LeanBlast.CourtadeKumar.large_curvature_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T11:12:55.94875+00:00
-- url     : https://prove2.me/theorems/0f6c0b32-f6b5-4700-b043-7a2927283bb9
-- title:
--   Curvature bound $h(u)^2\,\kappa(u)\le2/3$ for $u^2\ge2/3$
-- statement:
--   Let $h(u)=\log2-\psi(u)$, where $\psi(u)=\frac{1+u}2\log(1+u)+\frac{1-u}2\log(1-u)$. For every $u$ with $0\le u<1$ and $u^2\ge\frac23$,
--   $$
--   h(u)^2\cdot\frac{(1+u^2)\operatorname{artanh}u-u}{(1-u^2)^2(\operatorname{artanh}u)^3}\le\frac23 .
--   $$
--
--   This is the complementary range to the medium-curvature bound. Together they give the bound for all $u\in(0,1)$. With $s=\psi(u)$ and $x=\log2-s=h(u)$, the fraction is $r''(s)$. So the inequality says $x^2\,r''(\log2-x)\le\frac23$, a uniform curvature bound for the gap function $L$ that drives the convexity argument.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/BooleanNoise/LargeCurvature.lean#L62-L132

import Mathlib
import Definitions.Def_CourtadeKumar
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Model__CourtadeKumar
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Statement__CourtadeKumar
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Basic
import Definitions.Def_OAI_InformationTheory_BooleanNoise_FiniteNoise
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Statement
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropyScalars
import Definitions.Def_OAI_InformationTheory_BooleanNoise_FiniteDistribution
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Attainment
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Rearrangement
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CurvatureCertificates
import Definitions.Def_OAI_InformationTheory_BooleanNoise_ComparisonEstimates
import Definitions.Def_OAI_InformationTheory_BooleanNoise_InverseScalars
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropySeries
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropyBounds
import Definitions.Def_OAI_InformationTheory_BooleanNoise_MediumCurvature

open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open scoped BigOperators

theorem OAI.LeanBlast.CourtadeKumar.large_curvature_bound {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hu2 : (2 / 3 : ℝ) ≤ u ^ 2) :
    entropy u ^ 2 * (((1 + u ^ 2) * Real.artanh u - u) /
      ((1 - u ^ 2) ^ 2 * (Real.artanh u) ^ 3)) ≤ 2 / 3 := by sorry
