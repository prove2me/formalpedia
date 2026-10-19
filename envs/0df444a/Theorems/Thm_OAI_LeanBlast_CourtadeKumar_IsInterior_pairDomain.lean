-- Prove2me | Theorems.Thm_OAI_LeanBlast_CourtadeKumar_IsInterior_pairDomain
-- name    : OAI.LeanBlast.CourtadeKumar.IsInterior.pairDomain
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T11:17:42.169824+00:00
-- url     : https://prove2.me/theorems/f6e691d1-c48f-42d0-b51d-e7af8f5a713a
-- title:
--   Pair mean and half-difference of an interior function lie in the open diamond
-- statement:
--   Let $g:\{0,1\}^{n+1}\to\mathbb{R}$ with $-1<g<1$ everywhere. For $x\in\{0,1\}^n$, let $g_b(x)=g(b,x)$, $m(x)=\frac{g_1(x)+g_0(x)}2$ and $d(x)=\frac{g_1(x)-g_0(x)}2$. Then for every $x$,
--   $$
--   |m(x)|+|d(x)|<1 .
--   $$
--
--   The pair $(m,d)$ lies in the open diamond where the two-point entropy expressions $h(m\pm d)$ and $\operatorname{artanh}(m\pm d)$ are finite. This is the domain condition of the pairwise inequalities.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/BooleanNoise/CubeSplits.lean#L186-L202

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
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CurvatureBounds
import Definitions.Def_OAI_InformationTheory_BooleanNoise_LRegularity
import Definitions.Def_OAI_InformationTheory_BooleanNoise_SemigroupFlow
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CubeSplits

open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open scoped BigOperators
variable {n : ℕ}

theorem OAI.LeanBlast.CourtadeKumar.IsInterior.pairDomain {g : Cube (n + 1) → ℝ} (hg : IsInterior g) :
    ∀ x, |LeanBlast.CourtadeKumar.pairMean g x| + |pairHalfDifference g x| < 1 := by sorry
