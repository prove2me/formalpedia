-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_Typed_retained_loss_linear
-- name    : OAI.EntropyRateDimension.Typed.retained_loss_linear
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-19T05:10:35.140224+00:00
-- url     : https://prove2.me/theorems/2908815c-508f-433a-a1b3-a8eeee0ac435
-- title:
--   The retained entropy loss grows linearly
-- statement:
--   Let $f_i(x)=r_ix+b_i$ be a finite system with weights $w_i>0$ summing to $1$. For a word $w=w_0\cdots w_{n-1}$ write $f_w=f_{w_0}\circ\cdots\circ f_{w_{n-1}}$, $f_w(x)=a_wx+b_w$, and $w(w)=\prod_jw_{w_j}$. Fix a tag map on letters. The typed law $\nu_w$ of a word $w$ is the law of the offset $b_v$ for a random word $v$ with the same tags as $w$, drawn with probability proportional to $w(v)$. Its Shannon entropy and its entropy on the grid of mesh $\rho$ are measured in bits.
--
--   Suppose the tags determine the ratio, $\mu$ is a self-similar probability measure with $\bar H_s(\mu)\le D\log(1/s)+C$ for $s\in(0,1)$, $A>0$, $A'>\chi$, and
--   $$
--   DA\log2<h\log2-\log|\mathcal T|,
--   $$
--   where $h$ is the entropy rate and $\mathcal T$ the set of tags. Then there are $\varepsilon>0$ and $N$ such that for $n\ge N$ the loss at $\rho_n=2^{-\lceil An\rceil}$, averaged over words of depth at most $A'n$, is at least $\varepsilon n$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/RetainedLoss.lean#L100-L133

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

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.Typed
universe uα uβ
open FairPairs MeasureTheory MeasureEntropy
open scoped BigOperators ENNReal
variable {α : Type uα} {β : Type uβ} [Fintype α] [Nonempty α] [Fintype β] [DecidableEq β]

theorem OAI.EntropyRateDimension.Typed.retained_loss_linear (S : System α) (tag : α → β)
    (hr : ∀ a v, tag a=tag v → S.ratio a=S.ratio v)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : S.SelfSimilar μ)
    {D C A A' : ℝ} (hD : 0 ≤ D) (hA : 0 < A) (hA' : S.lyapunov < A')
    (hb : ∀ s, 0 < s → s < 1 → averaged μ s ≤ D*Real.log (1/s)+C)
    (hgap : D*A*Real.log 2 < S.entropyRate*Real.log 2-Real.log (Fintype.card β)) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ, 0 < N ∧ ∀ n, N ≤ n →
      ε*n ≤ retainedLoss S tag A A' n := by sorry
