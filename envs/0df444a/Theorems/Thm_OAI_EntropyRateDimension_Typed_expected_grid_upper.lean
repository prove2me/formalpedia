-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_Typed_expected_grid_upper
-- name    : OAI.EntropyRateDimension.Typed.expected_grid_upper
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-19T05:05:56.386981+00:00
-- url     : https://prove2.me/theorems/b8d9fd77-520d-4be4-a671-282344caa881
-- title:
--   Average typed grid entropy is at most the grid entropy of the measure
-- statement:
--   Let $f_i(x)=r_ix+b_i$ be a finite system with weights $w_i>0$ summing to $1$. For a word $w=w_0\cdots w_{n-1}$ write $f_w=f_{w_0}\circ\cdots\circ f_{w_{n-1}}$, $f_w(x)=a_wx+b_w$, and $w(w)=\prod_jw_{w_j}$. Fix a tag map on letters. The typed law $\nu_w$ of a word $w$ is the law of the offset $b_v$ for a random word $v$ with the same tags as $w$, drawn with probability proportional to $w(v)$. Its Shannon entropy and its entropy on the grid of mesh $\rho$ are measured in bits.
--
--   Suppose the tags determine the contraction ratio, and let $\mu$ be a compactly carried self-similar probability measure. For $\rho>0$ and every $n$, with $H_{\rho,0}(\mu)$ the entropy of $\lfloor x/\rho\rfloor$ under $\mu$ in natural units,
--   $$
--   \log2\sum_{|w|=n}w(w)\,H_\rho(\nu_w)\le H_{\rho,0}(\mu)+\log2 .
--   $$
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/TypedEntropy.lean#L120-L150

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

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.Typed
universe uα uβ uγ
open MeasureTheory FairPairs FiniteCondition FiniteEntropy MeasureEntropy
open scoped BigOperators ENNReal
variable {α : Type uα} {β : Type uβ} [Fintype α] [DecidableEq β]

theorem OAI.EntropyRateDimension.Typed.expected_grid_upper (S : System α) (tag : α → β)
    (hr : ∀ a v, tag a=tag v → S.ratio a=S.ratio v)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : S.SelfSimilar μ)
    (hc : CompactlyCarried μ) (n : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    (∑ w : Fin n → α, S.wordWeight w*(law S tag w).gridEntropy ρ)*Real.log 2 ≤
      grid μ ρ 0+Real.log 2 := by sorry
