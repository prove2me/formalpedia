-- Prove2me | Theorems.Thm_OAI_LeanBlast_CourtadeKumar_informationDeficit_eq_average_binaryRelativeEntropy
-- name    : OAI.LeanBlast.CourtadeKumar.informationDeficit_eq_average_binaryRelativeEntropy
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T11:28:42.867118+00:00
-- url     : https://prove2.me/theorems/ad763ec1-1e60-4ca3-b61a-da4422448fc2
-- title:
--   The information deficit is the average relative entropy to the mean
-- statement:
--   Let $g:\{0,1\}^n\to(-1,1)$ and $m=\mathbb{E}g$, the uniform average. With $h(v)=\log2-\psi(v)$ and the binary relative entropy
--   $$
--   D(a\|m)=\frac{1+a}{2}\log\frac{1+a}{1+m}+\frac{1-a}{2}\log\frac{1-a}{1-m},
--   $$
--   the theorem states
--   $$
--   h(\mathbb{E}g)-\mathbb{E}\,h(g)=\mathbb{E}\,D\bigl(g(x)\,\|\,\mathbb{E}g\bigr).
--   $$
--
--   The deficit is the mutual information between a uniform point $x$ and a sign drawn with mean $g(x)$. It equals the average divergence of the conditional laws from the marginal law, which is the standard formula for mutual information.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/BooleanNoise/CubeVariance.lean#L82-L102

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
import Definitions.Def_OAI_InformationTheory_BooleanNoise_JensenGaps
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CubeVariance

open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open scoped BigOperators
variable {n : ℕ}

theorem OAI.LeanBlast.CourtadeKumar.informationDeficit_eq_average_binaryRelativeEntropy
    {g : Cube n → ℝ} (hg : IsInterior g) :
    informationDeficit g =
      cubeAverage (fun x => binaryRelativeEntropy (g x) (cubeAverage g)) := by sorry
