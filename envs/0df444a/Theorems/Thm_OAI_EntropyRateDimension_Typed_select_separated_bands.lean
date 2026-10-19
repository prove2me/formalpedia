-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_Typed_select_separated_bands
-- name    : OAI.EntropyRateDimension.Typed.select_separated_bands
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T05:21:37.243056+00:00
-- url     : https://prove2.me/theorems/7d4e2a50-7679-45b2-9304-0dffc439b8bd
-- title:
--   Selecting scales with separated bands
-- statement:
--   Let $f_i(x)=r_ix+b_i$ be a finite system with weights $w_i>0$ summing to $1$, and fix a tag map on letters that determines the contraction ratio. For a word $w$ write $f_w(x)=a_wx+b_w$, $w(w)$ for its weight and $\mathrm{depth}(w)=-\log_2|a_w|$. The typed law $\nu_w$ is the law of the offset $b_v$ of a random word $v$ with the tags of $w$, and $\mathrm{cap}(\nu,\ell)$ is the capacity of the fair pairings of $\nu$ at distances in $[2^{-\ell},2^{1-\ell})$. The pair budget is $\mathrm{PB}_n(a,B)=\sum_{|w|=n,\ \mathrm{depth}(w)\le A'n}w(w)\sum_{\ell=a}^B\mathrm{cap}(\nu_w,\ell)$, and the band start is $\lceil An\rceil-1$.
--
--   Let $0<A$ and $A'<A$, and suppose every $n\ge N$ has a band $B\ge\lceil An\rceil-1$ with $cn\le\mathrm{PB}_n(\lceil An\rceil-1,B)$. Then for every $q$ there are lengths $n_1,\dots,n_q>0$ and bands $B_1,\dots,B_q$ with $\lceil An_i\rceil-1\ge1$, $c\,n_i\le\mathrm{PB}_{n_i}(\lceil An_i\rceil-1,B_i)$, and
--   $$
--   B_h<\lceil An_i\rceil-1-A'n_i-1\qquad(h<i).
--   $$
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/BandSelection.lean#L34-L78

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
open scoped BigOperators
variable {α : Type uα} {β : Type uβ} [Fintype α] [DecidableEq β]

theorem OAI.EntropyRateDimension.Typed.select_separated_bands (S : System α) (tag : α → β)
    {A A' c : ℝ} (hA : 0 < A) (hAA : A' < A) {N : ℕ}
    (hb : ∀ n, N ≤ n → ∃ B : ℤ, bandStart A n ≤ B ∧
      c*n ≤ pairBudget S tag A' (bandStart A n) B n) (q : ℕ) :
    ∃ n : Fin q → ℕ, ∃ B : Fin q → ℤ,
      (∀ i, 0 < n i) ∧ (∀ i, 1 ≤ bandStart A (n i)) ∧
      (∀ i, c*n i ≤ pairBudget S tag A' (bandStart A (n i)) (B i) (n i)) ∧
      (∀ i h : Fin q, h < i → (B h : ℝ)<(bandStart A (n i) : ℝ)-A'*n i-1) := by sorry
