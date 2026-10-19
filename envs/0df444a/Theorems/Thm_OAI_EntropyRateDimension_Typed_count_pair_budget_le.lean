-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_Typed_count_pair_budget_le
-- name    : OAI.EntropyRateDimension.Typed.count_pair_budget_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T05:20:43.034026+00:00
-- url     : https://prove2.me/theorems/547f256f-fc68-4068-a15d-9b37ce7e2021
-- title:
--   Global count: pair budgets over separated scales are bounded
-- statement:
--   Let $f_i(x)=r_ix+b_i$ be a finite system with weights $w_i>0$ summing to $1$, and fix a tag map on letters that determines the contraction ratio. For a word $w$ write $f_w(x)=a_wx+b_w$, $w(w)$ for its weight and $\mathrm{depth}(w)=-\log_2|a_w|$. The typed law $\nu_w$ is the law of the offset $b_v$ of a random word $v$ with the tags of $w$, and $\mathrm{cap}(\nu,\ell)$ is the capacity of the fair pairings of $\nu$ at distances in $[2^{-\ell},2^{1-\ell})$. Let $\mu$ be a compactly carried self-similar probability measure whose scale deficit $\log2-(\bar H_v(\mu)-\bar H_{2v}(\mu))$ is at least $\delta$ for all $v>0$. Fix $M>4$ with $\frac5M\log2\le\delta/2$, and write $\mathrm{W}(\lambda)=\bar H_s(\lambda)-\bar H_{M^2s}(\lambda)$ for the window at scale $s=2^{-L}/M$. The pair budget is $\mathrm{PB}_n(a,B)=\sum_{|w|=n,\ \mathrm{depth}(w)\le A'n}w(w)\sum_{\ell=a}^B\mathrm{cap}(\nu_w,\ell)$, and the band start is $\lceil An\rceil-1$.
--
--   Let letter depths be at most $D\ge1$. For finitely many scales $i$, let $K_in_i=H$, $a_i\ge1$, $B_i\le H$, and let the bands be separated, $B_h<a_i-A'n_i-1$ for $h<i$. Then
--   $$
--   \frac\delta2\sum_iK_i\,\mathrm{PB}_{n_i}(a_i,B_i)\le2DH\log(M^2) .
--   $$
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/GlobalCount.lean#L34-L96

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
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_WindowGain

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.Typed
universe uα uβ
open MeasureTheory MeasureEntropy FairPairs Windows
open scoped BigOperators ENNReal
variable {α : Type uα} {β : Type uβ} [Fintype α] [DecidableEq β]

theorem OAI.EntropyRateDimension.Typed.count_pair_budget_le (S : System α) (tag : α → β)
    (hr : ∀ a v, tag a=tag v → S.ratio a=S.ratio v)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : S.SelfSimilar μ)
    (hc : CompactlyCarried μ) {δ : ℝ}
    (hδ : ∀ v, 0 < v → δ ≤ deficit μ v) {M : ℕ} (hM : 4 < M)
    (he : 5/(M : ℝ)*Real.log 2 ≤ δ/2)
    {H D q : ℕ} (hD : 1 ≤ D) (hd : ∀ v, S.letterDepth v ≤ D)
    (n K : Fin q → ℕ) (a B : Fin q → ℤ) (A' : ℝ)
    (hkn : ∀ i, K i*n i=H) (ha : ∀ i, 1 ≤ a i) (hB : ∀ i, B i ≤ (H : ℤ))
    (hsep : ∀ i h : Fin q, h < i → (B h : ℝ)<(a i : ℝ)-A'*n i-1) :
    (δ/2)*(∑ i, (K i : ℝ)*pairBudget S tag A' (a i) (B i) (n i)) ≤
      (2*D*H : ℕ)*Real.log ((M*M : ℕ) : ℝ) := by sorry
