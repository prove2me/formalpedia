-- Prove2me | Theorems.Thm_OAI_LeanBlast_CourtadeKumar_hasSum_lambda
-- name    : OAI.LeanBlast.CourtadeKumar.hasSum_lambda
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T11:23:55.220343+00:00
-- url     : https://prove2.me/theorems/9810c022-751a-41f7-a235-637cbf97be1a
-- title:
--   Series of $\lambda(z)=-\log(1-z)/z$
-- statement:
--   Let $\lambda(z)=-\log(1-z)/z$ for $z\ne0$ and $\lambda(0)=1$. For every $z$ with $0\le z<1$,
--   $$
--   \lambda(z)=\sum_{j=0}^{\infty}\frac{z^j}{j+1},
--   $$
--   the series converging.
--
--   The positive series gives monotone truncation bounds for $\lambda$, used in the one-variable inequalities of the perspective argument.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/BooleanNoise/LambdaScalars.lean#L27-L41

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
import Definitions.Def_OAI_InformationTheory_BooleanNoise_PairEntropy
import Definitions.Def_OAI_InformationTheory_BooleanNoise_LambdaScalars

open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open scoped BigOperators Topology
open Set Filter

theorem OAI.LeanBlast.CourtadeKumar.hasSum_lambda {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) :
    HasSum (fun j : ℕ => z ^ j / ((j : ℝ) + 1)) (lambda z) := by sorry
