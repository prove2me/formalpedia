-- Prove2me | Theorems.Thm_OAI_LeanBlast_CourtadeKumar_lambda_truncated_upper
-- name    : OAI.LeanBlast.CourtadeKumar.lambda_truncated_upper
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T11:34:13.968384+00:00
-- url     : https://prove2.me/theorems/0801578f-eefa-4768-bd02-ea26e52c928b
-- title:
--   Truncated upper bounds for $(1-z^k)\lambda(z)$
-- statement:
--   Let $\lambda(z)=-\log(1-z)/z$, with $\lambda(0)=1$, and let $0\le z<1$ and $k,m\in\mathbb{N}$. Then
--   $$
--   (1-z^k)\lambda(z)\le\sum_{j<k}\frac{z^j}{j+1}-\sum_{j<m}\Bigl(\frac{z^{k+j}}{j+1}-\frac{z^{j+k}}{j+k+1}\Bigr).
--   $$
--
--   Each subtracted term is nonnegative, so taking more terms ($m$ larger) gives sharper explicit upper bounds for $(1-z^k)\lambda(z)$. These feed polynomial certificates for the $\lambda$-inequalities.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/BooleanNoise/PerspectiveInequality.lean#L35-L54

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
import Definitions.Def_OAI_InformationTheory_BooleanNoise_NormalizedPair
import Definitions.Def_OAI_InformationTheory_BooleanNoise_PerspectiveLogTrapezoid
import Definitions.Def_OAI_InformationTheory_BooleanNoise_PerspectiveCalculus
import Definitions.Def_OAI_InformationTheory_BooleanNoise_PerspectiveInequality

open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open scoped BigOperators Topology
open Set Filter

theorem OAI.LeanBlast.CourtadeKumar.lambda_truncated_upper {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) (k m : ℕ) :
    (1 - z ^ k) * lambda z ≤
      (∑ j ∈ Finset.range k, z ^ j / ((j : ℝ) + 1)) -
      ∑ j ∈ Finset.range m,
        (z ^ k * (z ^ j / ((j : ℝ) + 1)) -
          z ^ (j + k) / ((j : ℝ) + k + 1)) := by sorry
