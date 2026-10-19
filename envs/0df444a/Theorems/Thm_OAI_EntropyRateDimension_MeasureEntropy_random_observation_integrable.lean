-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_MeasureEntropy_random_observation_integrable
-- name    : OAI.EntropyRateDimension.MeasureEntropy.random_observation_integrable
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T05:05:14.38296+00:00
-- url     : https://prove2.me/theorems/4339070f-0a4e-407b-add4-ebd8bd7d84d5
-- title:
--   Integrability of the entropy of a random observation
-- statement:
--   Let $\mu$ be a probability measure on $X$, $p_i\ge0$ weights summing to $1$ on a finite index set, and $f_i:X\to\mathbb Z$ measurable with $f_i(y)$ in a fixed finite set $s$ for almost every $y$. Then the function
--   $$
--   y\mapsto H_p\bigl(i\mapsto f_i(y)\bigr)
--   $$
--   is $\mu$-integrable, where $H_p$ is the entropy of the law of the observation under $p$.
--
--   This makes the averaged entropy above well defined.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/KernelEntropy.lean#L96-L124

import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RandomGrid
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Boundary
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TranslationGain
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FairPairs
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ProductLaw
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_GridCoupling
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteRefinement
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_SumsetBound
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_WordTypes
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_DigitSumset
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Bernoulli
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Coding
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_InvariantLaw
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BallRatios
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BallIntegrability
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_CodingIntegrals
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ErgodicAverages
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TriangularAverages
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BallLimits
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RadiusGrowth
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RadialLimit
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ExactDimension
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_UpperBound
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Conditioning
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_PairGain
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TypedLaw
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TailConvolution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteVariance
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_SuffixLaw
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_WordAverage

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.MeasureEntropy
universe uα uβ uX
open MeasureTheory
open scoped BigOperators ENNReal

theorem OAI.EntropyRateDimension.MeasureEntropy.random_observation_integrable {X : Type uX} {α : Type uα} [MeasurableSpace X] [Fintype α]
    (μ : Measure X) [IsProbabilityMeasure μ] (p : α → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i=1)
    (f : α → X → ℤ) (hf : ∀ i, Measurable (f i)) (s : Finset ℤ)
    (hs : ∀ i, ∀ᵐ y ∂μ, f i y ∈ s) :
    Integrable (fun y => FiniteEntropy.observableEntropy Finset.univ p (fun i => f i y)) μ := by sorry
