-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_Windows_retained_sum_le
-- name    : OAI.EntropyRateDimension.Windows.retained_sum_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T05:14:48.256113+00:00
-- url     : https://prove2.me/theorems/9947a7d7-241c-45d6-9025-f6e2aa3fe1b0
-- title:
--   Retained window drops over separated scales sum to at most the start
-- statement:
--   Let $\sigma$ be a nondecreasing sequence and $g$ a nonincreasing nonnegative sequence on $\mathbb N$. For finitely many scales $i$ take lengths $n_i$, counts $K_i$ and bands $[a_i,B_i]$, separated so that $B_h<a_i-A'n_i-1$ whenever $h<i$. Call $j$ retained for scale $i$ and target $L$ if $\sigma(j+n_i)-\sigma(j)\le A'n_i$ and $a_i\le L-\lceil\sigma(j)\rceil\le B_i$. Then
--   $$
--   \sum_i\sum_{k<K_i}[kn_i\text{ retained}]\,\bigl(g(kn_i)-g(kn_i+n_i)\bigr)\le g(0) .
--   $$
--
--   The separation of bands makes all retained windows pairwise disjoint, so their drops cannot add up beyond the total available drop.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/WindowCount.lean#L11-L50

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

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.Windows
open scoped BigOperators

theorem OAI.EntropyRateDimension.Windows.retained_sum_le {q : ℕ} (n K : Fin q → ℕ) (a B : Fin q → ℤ) (A' : ℝ)
    (hsep : ∀ i h : Fin q, h < i → (B h : ℝ)<(a i : ℝ)-A'*n i-1)
    (σ : ℕ → ℝ) (hσ : Monotone σ) (L : ℤ)
    (g : ℕ → ℝ) (hg : Antitone g) (hgn : ∀ j, 0 ≤ g j) :
    (∑ i, ∑ k ∈ Finset.range (K i),
      if Retained σ A' (n i) (a i) (B i) L (k*n i) then
        g (k*n i)-g (k*n i+n i) else 0) ≤ g 0 := by sorry
