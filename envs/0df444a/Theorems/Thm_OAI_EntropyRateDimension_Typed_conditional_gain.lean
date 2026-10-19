-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_Typed_conditional_gain
-- name    : OAI.EntropyRateDimension.Typed.conditional_gain
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T05:16:26.984442+00:00
-- url     : https://prove2.me/theorems/a57fe61c-ea9e-4c92-beba-490365387bde
-- title:
--   A band of the typed law raises the window of the scaled tail
-- statement:
--   Let $f_i(x)=r_ix+b_i$ be a finite system with weights $w_i>0$ summing to $1$, and fix a tag map on letters that determines the contraction ratio. For a word $w$ write $f_w(x)=a_wx+b_w$, $w(w)$ for its weight and $\mathrm{depth}(w)=-\log_2|a_w|$. The typed law $\nu_w$ is the law of the offset $b_v$ of a random word $v$ with the tags of $w$, and $\mathrm{cap}(\nu,\ell)$ is the capacity of the fair pairings of $\nu$ at distances in $[2^{-\ell},2^{1-\ell})$. Let $\mu$ be a compactly carried self-similar probability measure whose scale deficit $\log2-(\bar H_v(\mu)-\bar H_{2v}(\mu))$ is at least $\delta$ for all $v>0$. Fix $M>4$ with $\frac5M\log2\le\delta/2$, and write $\mathrm{W}(\lambda)=\bar H_s(\lambda)-\bar H_{M^2s}(\lambda)$ for the window at scale $s=2^{-L}/M$. The scaled tail of a word $y$ at scale $\lambda$ is $(x\mapsto\lambda x)_*\mathrm{tail}_y(\mu)$, where $\mathrm{tail}_y(\mu)$ mixes $(f_v)_*\mu$ over words $v$ with the tags of $y$.
--
--   For words $u,w$, any length $t$ and target band $L$,
--   $$
--   \frac\delta2\,\mathrm{cap}\bigl(\nu_w,\ L-\lceil\mathrm{depth}(u)\rceil\bigr)\le\sum_{|z|=t}w(z)\Bigl(\mathrm{W}\bigl(\mathrm{ST}_{a_u}(wz)\bigr)-\mathrm{W}\bigl(\mathrm{ST}_{a_ua_w}(z)\bigr)\Bigr),
--   $$
--   where $\mathrm{ST}_\lambda(y)$ denotes the scaled tail of $y$ at scale $\lambda$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/ScaleGain.lean#L82-L113

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
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BlockWords
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_EntropyBudget
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RetainedLoss
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_PairBands
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_WindowCount

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.Typed
universe uα uβ
open scoped BigOperators ENNReal
open MeasureTheory FairPairs MeasureEntropy
variable {α : Type uα} {β : Type uβ} [Fintype α] [DecidableEq β]

theorem OAI.EntropyRateDimension.Typed.conditional_gain (S : System α) (tag : α → β)
    (hr : ∀ a v, tag a=tag v → S.ratio a=S.ratio v)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : S.SelfSimilar μ)
    (hc : CompactlyCarried μ) {δ : ℝ}
    (hδ : ∀ v, 0 < v → δ ≤ deficit μ v) {M : ℕ} (hM : 4 < M)
    (he : 5/(M : ℝ)*Real.log 2 ≤ δ/2)
    {j n : ℕ} (u : Fin j → α) (w : Fin n → α) (t : ℕ) (L : ℤ) :
    δ/2*capacity (law S tag w) (L-⌈S.wordDepth u⌉) ≤
      ∑ z : Fin t → α, S.wordWeight z*
        (window (scaledTail S tag μ (S.completeMap u).1 (Fin.append w z))
          ((2 : ℝ)^(-L)/M) (((M*M : ℕ) : ℝ)*((2 : ℝ)^(-L)/M))-
        window (scaledTail S tag μ ((S.completeMap u).1*(S.completeMap w).1) z)
          ((2 : ℝ)^(-L)/M) (((M*M : ℕ) : ℝ)*((2 : ℝ)^(-L)/M))) := by sorry
