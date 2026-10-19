-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_Typed_entropyLoss_le
-- name    : OAI.EntropyRateDimension.Typed.entropyLoss_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T05:09:32.809784+00:00
-- url     : https://prove2.me/theorems/8c3a93da-0671-4180-ad14-6c98bac17d29
-- title:
--   The grid entropy loss of a word is at most linear
-- statement:
--   Let $f_i(x)=r_ix+b_i$ be a finite system with weights $w_i>0$ summing to $1$. For a word $w=w_0\cdots w_{n-1}$ write $f_w=f_{w_0}\circ\cdots\circ f_{w_{n-1}}$, $f_w(x)=a_wx+b_w$, and $w(w)=\prod_jw_{w_j}$. Fix a tag map on letters. The typed law $\nu_w$ of a word $w$ is the law of the offset $b_v$ for a random word $v$ with the same tags as $w$, drawn with probability proportional to $w(v)$. Its Shannon entropy and its entropy on the grid of mesh $\rho$ are measured in bits.
--
--   The entropy loss at scale $\rho$, $\mathrm{loss}_\rho(w)=\bigl(H(\nu_w)-H_\rho(\nu_w)\bigr)\log2$, satisfies for every word $w$ of length $n$
--   $$
--   \mathrm{loss}_\rho(w)\le n\log|\Sigma|,
--   $$
--   where $\Sigma$ is the alphabet.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/EntropyBudget.lean#L55-L88

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

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.Typed
universe uα uβ
open FiniteEntropy FairPairs FiniteCondition MeasureEntropy MeasureTheory
open scoped BigOperators ENNReal
variable {α : Type uα} {β : Type uβ} [Fintype α] [Fintype β] [DecidableEq β]

omit [Fintype β] in
theorem OAI.EntropyRateDimension.Typed.entropyLoss_le (S : System α) (tag : α → β) {n : ℕ}
    (w : Fin n → α) (ρ : ℝ) :
    entropyLoss S tag w ρ ≤ (n : ℝ)*Real.log (Fintype.card α) := by sorry
