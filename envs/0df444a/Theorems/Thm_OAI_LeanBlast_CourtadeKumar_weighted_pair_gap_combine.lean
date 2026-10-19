-- Prove2me | Theorems.Thm_OAI_LeanBlast_CourtadeKumar_weighted_pair_gap_combine
-- name    : OAI.LeanBlast.CourtadeKumar.weighted_pair_gap_combine
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T11:27:52.967737+00:00
-- url     : https://prove2.me/theorems/5cddcd56-9f87-4964-b3f5-9b7372e628de
-- title:
--   Combining the two perspective halves into a pair-entropy-gap inequality
-- statement:
--   Let $\psi(v)=\frac{1+v}{2}\log(1+v)+\frac{1-v}{2}\log(1-v)$ and $h(v)=\log2-\psi(v)$. The pair entropy gap is $\Delta(a,b)=h(a)-\frac{h(a+b)+h(a-b)}{2}$. Let $\iota$ be finite, $w,a,b:\iota\to\mathbb{R}$ with $|a_i|+|b_i|<1$, and $m,k,C\in\mathbb{R}$ with $|m|+|k|<1$. Suppose the two perspective inequalities hold, for the sign $\pm=+$ and for $\pm=-$:
--   $$
--   \Bigl(\sum_iw_i\frac{b_i^2}{1\pm a_i}-\frac{k^2}{1\pm m}\Bigr)C\le2\Bigl(\sum_iw_i(1\pm a_i)\psi\Bigl(\frac{b_i}{1\pm a_i}\Bigr)-(1\pm m)\psi\Bigl(\frac{k}{1\pm m}\Bigr)\Bigr).
--   $$
--   Then
--   $$
--   \Bigl(\sum_iw_i\frac{b_i^2}{1-a_i^2}-\frac{k^2}{1-m^2}\Bigr)C\le2\Bigl(\sum_iw_i\Delta(a_i,b_i)-\Delta(m,k)\Bigr).
--   $$
--
--   This is the averaging step of the induction. It compares the pair entropy gaps at the parent level with those of the children.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/BooleanNoise/JensenGaps.lean#L356-L390

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

open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open scoped BigOperators
universe u
variable {ι : Type u} [Fintype ι]

theorem OAI.LeanBlast.CourtadeKumar.weighted_pair_gap_combine (w a b : ι → ℝ) (m k C : ℝ)
    (hdom : ∀ i, |a i| + |b i| < 1) (hcenter : |m| + |k| < 1)
    (hp : ((∑ i, w i * (b i) ^ 2 / (1 + a i)) - k ^ 2 / (1 + m)) * C ≤
      2 * ((∑ i, w i * (1 + a i) * psi (b i / (1 + a i))) -
        (1 + m) * psi (k / (1 + m))))
    (hm : ((∑ i, w i * (b i) ^ 2 / (1 - a i)) - k ^ 2 / (1 - m)) * C ≤
      2 * ((∑ i, w i * (1 - a i) * psi (b i / (1 - a i))) -
        (1 - m) * psi (k / (1 - m)))) :
    ((∑ i, w i * (b i) ^ 2 / (1 - (a i) ^ 2)) - k ^ 2 / (1 - m ^ 2)) * C ≤
      2 * ((∑ i, w i * pairEntropyGap (a i) (b i)) - pairEntropyGap m k) := by sorry
