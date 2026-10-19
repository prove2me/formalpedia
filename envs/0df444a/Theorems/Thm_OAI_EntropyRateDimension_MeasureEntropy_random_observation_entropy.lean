-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_MeasureEntropy_random_observation_entropy
-- name    : OAI.EntropyRateDimension.MeasureEntropy.random_observation_entropy
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T05:02:36.803824+00:00
-- url     : https://prove2.me/theorems/c2c3f399-d78d-4324-afff-d30f05eca998
-- title:
--   Expected entropy of a random observation is at most the mixture entropy
-- statement:
--   Let $\mu$ be a probability measure on $X$, $p_i\ge0$ weights summing to $1$ on a finite set, and $F_i:X\to\mathbb R$ measurable. Let $\nu=\sum_ip_i(F_i)_*\mu$, and let $f:\mathbb R\to\mathbb Z$ be measurable with $f(F_i(y))$ in a finite set $s$ for almost every $y$. Then
--   $$
--   \int H_p\bigl(i\mapsto f(F_i(y))\bigr)\,d\mu(y)\le H_\nu(f),
--   $$
--   where $H_p(g)$ is the entropy of the law of $g$ under $p$, and $H_\nu(f)$ that of $f$ under $\nu$.
--
--   This is concavity of entropy, applied to a random choice of observation.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/KernelEntropy.lean#L33-L94

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

theorem OAI.EntropyRateDimension.MeasureEntropy.random_observation_entropy {X : Type uX} {α : Type uα} [MeasurableSpace X] [Fintype α]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (p : α → ℝ) (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i=1)
    (F : α → X → ℝ) (hF : ∀ i, Measurable (F i))
    (hm : ν=∑ i, ENNReal.ofReal (p i) • μ.map (F i))
    (f : ℝ → ℤ) (hf : Measurable f) (s : Finset ℤ)
    (hs : ∀ i, ∀ᵐ y ∂μ, f (F i y) ∈ s) :
    (∫ y, FiniteEntropy.observableEntropy Finset.univ p (fun i => f (F i y)) ∂μ) ≤ entropy ν f := by sorry
