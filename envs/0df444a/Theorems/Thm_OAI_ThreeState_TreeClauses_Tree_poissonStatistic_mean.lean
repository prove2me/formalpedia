-- Prove2me | Theorems.Thm_OAI_ThreeState_TreeClauses_Tree_poissonStatistic_mean
-- name    : OAI.ThreeState.TreeClauses.Tree.poissonStatistic_mean
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T20:17:41.964192+00:00
-- url     : https://prove2.me/theorems/d79907a2-edd7-4017-9ed3-f361417ef7ca
-- title:
--   The normalized boundary statistic of the Poisson broadcast tree is unbiased for the root score
-- statement:
--   Spins are elements of $\{0,1,2\}$, and $\lambda$ is admissible if $-\tfrac12\le\lambda\le1$. The channel $M_\lambda(i,\cdot)$ keeps the spin with probability $\tfrac{1+2\lambda}{3}$ and moves it to each other spin with probability $\tfrac{1-\lambda}{3}$. The spin score is $\sigma(0)=2$, $\sigma(1)=\sigma(2)=-1$.
--
--   Ordered Galton–Watson observations are defined as follows. A depth-$0$ ordered observation is a spin. A depth-$(\ell+1)$ ordered observation is a pair $(n,v)$ of a child count $n$ and an $n$-tuple $v$ of depth-$\ell$ ordered observations. Under the ordered law $\mathcal O_\ell(i)$ with offspring law $\rho$: $\mathcal O_0(i)$ is the point mass at $i$. To sample $\mathcal O_{\ell+1}(i)$, draw $n\sim\rho$ and then $n$ independent copies of "$j\sim M_\lambda(i,\cdot)$, then $\mathcal O_\ell(j)$". Let $d\ge0$ and let $\rho=\mathrm{Poi}(d)$, with $\rho(n)=e^{-d}d^n/n!$. The normalized boundary statistic is $S_0(i)=\sigma(i)$ and $S_{\ell+1}(n,v)=\frac1{d\lambda}\sum_{j<n}S_\ell(v_j)$. Assume $d\ne0$ and $\lambda\ne0$ admissible. Then for every depth $\ell$ and root spin $i$, under the ordered Poisson law,
--   $$
--   \mathbb{E}_{\mathcal O_\ell(i)}\bigl[S_\ell\bigr]=\sigma(i).
--   $$
--
--   The statistic $S_\ell$ is $(d\lambda)^{-\ell}$ times the sum of the spin scores of generation $\ell$. Its mean equals the root's spin score at every depth, which is the signal part of the Kesten–Stigum argument for Poisson trees.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThreeStateClauses/PoissonReconstruction.lean#L62-L89

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
import Definitions.Def_OAI_Probability_ThreeStateClauses_InformationLoss
import Definitions.Def_OAI_Probability_ThreeStateClauses_RegularReconstruction
import Definitions.Def_OAI_Probability_ThreeStateClauses_ObservedMixtures
import Definitions.Def_OAI_Probability_ThreeStateClauses_OffspringLaws
import Definitions.Def_OAI_Probability_ThreeStateClauses_PoissonReconstruction

open OAI OAI.ThreeState OAI.ThreeState.TreeClauses OAI.ThreeState.TreeClauses.Tree
open scoped BigOperators ENNReal NNReal Topology
open Filter
open Set MeasureTheory
open scoped BigOperators NNReal
open ThreeState.TreeClauses.Experiment ThreeState.TreeClauses.Probability

theorem OAI.ThreeState.TreeClauses.Tree.poissonStatistic_mean (d : ℝ≥0) (hd : (d:ℝ) ≠ 0) (lam : ℝ) (hlam : Admissible lam)
    (hl : lam ≠ 0) (ℓ : ℕ) (i : Spin) :
    (∫ v, orderedStatistic d lam ℓ v
      ∂(orderedLaw (poissonPMF d) lam hlam ℓ i).toMeasure) = spinScore i := by sorry
