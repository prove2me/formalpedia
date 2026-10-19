-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_Typed_expected_capacity_targets
-- name    : OAI.EntropyRateDimension.Typed.expected_capacity_targets
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T05:19:53.116307+00:00
-- url     : https://prove2.me/theorems/85aa2646-ba71-471f-b5f7-611b66f151db
-- title:
--   Summing retained capacities over targets gives the pair budget
-- statement:
--   Let $f_i(x)=r_ix+b_i$ be a finite system with weights $w_i>0$ summing to $1$, and fix a tag map on letters that determines the contraction ratio. For a word $w$ write $f_w(x)=a_wx+b_w$, $w(w)$ for its weight and $\mathrm{depth}(w)=-\log_2|a_w|$. The typed law $\nu_w$ is the law of the offset $b_v$ of a random word $v$ with the tags of $w$, and $\mathrm{cap}(\nu,\ell)$ is the capacity of the fair pairings of $\nu$ at distances in $[2^{-\ell},2^{1-\ell})$. The pair budget is $\mathrm{PB}_n(a,B)=\sum_{|w|=n,\ \mathrm{depth}(w)\le A'n}w(w)\sum_{\ell=a}^B\mathrm{cap}(\nu_w,\ell)$, and the band start is $\lceil An\rceil-1$.
--
--   Let $j+n\le H$, $a\ge1$, and suppose every prefix depth satisfies $0\le\lceil\mathrm{depth}(W_{<j})\rceil$ and $B+\lceil\mathrm{depth}(W_{<j})\rceil\le T$. Then summing the expected retained capacities over all targets $L\in[1,T]$ gives
--   $$
--   \sum_{L=1}^T\mathbb E_H\bigl[\mathrm{rc}_j^{(L)}\bigr]=\mathrm{PB}_n(a,B) .
--   $$
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/WindowGain.lean#L94-L113

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

theorem OAI.EntropyRateDimension.Typed.expected_capacity_targets (S : System α) (tag : α → β)
    {H j n : ℕ} (hH : j+n ≤ H) (A' : ℝ) (a B T : ℤ)
    (ha : 1 ≤ a)
    (hcover : ∀ W : List α, 0 ≤ ⌈S.listDepth (W.take j)⌉ ∧ B+⌈S.listDepth (W.take j)⌉ ≤ T) :
    (∑ L ∈ Finset.Icc 1 T, S.wordAverage H (fun W => retainedCapacity S tag A' n a B L W j))=
      pairBudget S tag A' a B n := by sorry
