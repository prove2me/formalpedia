-- Prove2me | Theorems.Thm_OAI_ThreeState_TreeClauses_Tree_poissonStatistic_second
-- name    : OAI.ThreeState.TreeClauses.Tree.poissonStatistic_second
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T20:19:22.132324+00:00
-- url     : https://prove2.me/theorems/577560ce-6889-47f0-bd80-234c27ea5519
-- title:
--   Above the Kesten–Stigum threshold the Poisson boundary statistic has second moment at most $4d\lambda^2/(d\lambda^2-1)$
-- statement:
--   Spins are elements of $\{0,1,2\}$, and $\lambda$ is admissible if $-\tfrac12\le\lambda\le1$. The channel $M_\lambda(i,\cdot)$ keeps the spin with probability $\tfrac{1+2\lambda}{3}$ and moves it to each other spin with probability $\tfrac{1-\lambda}{3}$. The spin score is $\sigma(0)=2$, $\sigma(1)=\sigma(2)=-1$.
--
--   Ordered Galton–Watson observations are defined as follows. A depth-$0$ ordered observation is a spin. A depth-$(\ell+1)$ ordered observation is a pair $(n,v)$ of a child count $n$ and an $n$-tuple $v$ of depth-$\ell$ ordered observations. Under the ordered law $\mathcal O_\ell(i)$ with offspring law $\rho$: $\mathcal O_0(i)$ is the point mass at $i$. To sample $\mathcal O_{\ell+1}(i)$, draw $n\sim\rho$ and then $n$ independent copies of "$j\sim M_\lambda(i,\cdot)$, then $\mathcal O_\ell(j)$". Let $d\ge0$ and let $\rho=\mathrm{Poi}(d)$, with $\rho(n)=e^{-d}d^n/n!$. The normalized boundary statistic is $S_0(i)=\sigma(i)$ and $S_{\ell+1}(n,v)=\frac1{d\lambda}\sum_{j<n}S_\ell(v_j)$. Assume the Kesten–Stigum condition $d\lambda^2>1$. Then for every depth $\ell$ and root spin $i$, under the ordered Poisson law,
--   $$
--   \mathbb{E}_{\mathcal O_\ell(i)}\bigl[S_\ell^2\bigr]\le\kappa(d,\lambda):=\frac{4\,d\lambda^2}{d\lambda^2-1}.
--   $$
--
--   The noise of the normalized boundary statistic stays bounded uniformly in the depth exactly above the Kesten–Stigum threshold. Combined with unbiasedness, this yields a uniform positive lower bound on the reconstruction advantage.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThreeStateClauses/PoissonReconstruction.lean#L114-L160

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
open Set MeasureTheory Filter
open scoped BigOperators Topology NNReal
open ThreeState.TreeClauses.Experiment ThreeState.TreeClauses.Probability

theorem OAI.ThreeState.TreeClauses.Tree.poissonStatistic_second (d : ℝ≥0) (lam : ℝ) (hlam : Admissible lam)
    (hKS : 1 < (d:ℝ)*lam^2) (ℓ : ℕ) (i : Spin) :
    (∫ v, orderedStatistic d lam ℓ v^2
      ∂(orderedLaw (poissonPMF d) lam hlam ℓ i).toMeasure) ≤ poissonKSConstant d lam := by sorry
