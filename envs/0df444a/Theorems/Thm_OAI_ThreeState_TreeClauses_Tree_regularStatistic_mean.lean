-- Prove2me | Theorems.Thm_OAI_ThreeState_TreeClauses_Tree_regularStatistic_mean
-- name    : OAI.ThreeState.TreeClauses.Tree.regularStatistic_mean
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T20:11:07.017483+00:00
-- url     : https://prove2.me/theorems/06aca0f7-25ea-4603-b584-4e08888d817f
-- title:
--   The normalized boundary statistic of the $b$-ary broadcast tree is unbiased for the root score
-- statement:
--   Spins are elements of $\{0,1,2\}$, and $\lambda$ is admissible if $-\tfrac12\le\lambda\le1$. The channel $M_\lambda(i,\cdot)$ keeps the spin with probability $\tfrac{1+2\lambda}{3}$ and moves it to each other spin with probability $\tfrac{1-\lambda}{3}$. The spin score is $\sigma(0)=2$, $\sigma(1)=\sigma(2)=-1$.
--
--   Let $b\ge1$ and let $\lambda\ne0$ be admissible. Let $\mathcal R_\ell(i)$ be the ordered $b$-ary observation law: $\mathcal R_0(i)$ is the point mass at $i$, and $\mathcal R_{\ell+1}(i)$ is the product of $b$ independent copies of "$j\sim M_\lambda(i,\cdot)$, then $\mathcal R_\ell(j)$". Let $T_0=\sigma$ and $T_{\ell+1}(v_0,\dots,v_{b-1})=\frac1{b\lambda}\sum_jT_\ell(v_j)$. Then for every depth $\ell$ and root spin $i$,
--   $$
--   \mathbb{E}_{\mathcal R_\ell(i)}\bigl[T_\ell\bigr]=\sigma(i).
--   $$
--
--   $T_\ell$ is $(b\lambda)^{-\ell}$ times the sum of the spin scores of the $b^\ell$ leaves. The normalization makes it an unbiased estimator of the root's spin score, the first ingredient of the Kesten–Stigum argument.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThreeStateClauses/RegularStatistics.lean#L112-L126

import Mathlib
import Definitions.Def_ThreeStateTreeClauses
import Definitions.Def_OAI_Probability_ThreeStateClauses_RadialAlgebra
import Definitions.Def_OAI_Probability_ThreeStateClauses_PosteriorLaw
import Definitions.Def_OAI_Probability_ThreeStateClauses_DiscreteLaw
import Definitions.Def_OAI_Probability_ThreeStateClauses_Products
import Definitions.Def_OAI_Probability_ThreeStateClauses_Degradation
import Definitions.Def_OAI_Probability_ThreeStateClauses_RegularLaw
import Definitions.Def_OAI_Probability_ThreeStateClauses_BranchMoments
import Definitions.Def_OAI_Probability_ThreeStateClauses_CompactLimits
import Definitions.Def_OAI_Probability_ThreeStateClauses_RegularStatistics

open OAI OAI.ThreeState OAI.ThreeState.TreeClauses OAI.ThreeState.TreeClauses.Tree
open scoped BigOperators ENNReal NNReal Topology
open Filter
open Set MeasureTheory
open scoped BigOperators
open ThreeState.TreeClauses.Experiment

theorem OAI.ThreeState.TreeClauses.Tree.regularStatistic_mean (b : ℕ) (hb : 0 < b) (lam : ℝ) (hlam : Admissible lam)
    (hl : lam ≠ 0) (ℓ : ℕ) (i : Spin) :
    (∫ v, regularStatistic b lam ℓ v ∂(regularLaw b lam hlam ℓ i).toMeasure) = spinScore i := by sorry
