-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_System_depth_bad_mass_bound
-- name    : OAI.EntropyRateDimension.System.depth_bad_mass_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:57:47.377244+00:00
-- url     : https://prove2.me/theorems/4076b309-b43b-4a5f-9eba-bec7dceecf73
-- title:
--   Chebyshev bound for deep words
-- statement:
--   Let $f_i(x)=r_ix+b_i$ have weights $w_i$, letter depths $d_i=-\log_2|r_i|$, Lyapunov exponent $\chi=\sum_iw_id_i$ and depth variance $\sigma^2=\sum_iw_i(d_i-\chi)^2$. For $A>\chi$ and $n\ge1$, the total weight of words of length $n$ with depth $-\log_2|a_w|$ greater than $An$ satisfies
--   $$
--   \sum_{|w|=n,\ \mathrm{depth}(w)>An}w(w)\le\frac{\sigma^2}{n\,(A-\chi)^2} .
--   $$
--
--   So words deeper than $An$ have vanishing total weight as $n\to\infty$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/FiniteVariance.lean#L85-L109

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

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.System
universe uα
open scoped BigOperators
variable {α : Type uα} [Fintype α]

theorem OAI.EntropyRateDimension.System.depth_bad_mass_bound (S : System α) {A : ℝ} (hA : S.lyapunov < A)
    {n : ℕ} (hn : 0 < n) :
    (∑ w : Fin n → α, if A*n < S.wordDepth w then S.wordWeight w else 0) ≤
      S.depthVariance/((n : ℝ)*(A-S.lyapunov)^2) := by sorry
