-- Prove2me | Theorems.Thm_OAI_ThreeState_TreeClauses_Tree_orderedLaw_forget
-- name    : OAI.ThreeState.TreeClauses.Tree.orderedLaw_forget
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T20:14:09.671655+00:00
-- url     : https://prove2.me/theorems/007e789d-c8d0-4d4a-a207-564005ce1d01
-- title:
--   Forgetting child order in the ordered Galton–Watson broadcast law gives the observation law
-- statement:
--   Spins are elements of $\{0,1,2\}$, and $\lambda$ is admissible if $-\tfrac12\le\lambda\le1$. The channel $M_\lambda(i,\cdot)$ keeps the spin with probability $\tfrac{1+2\lambda}{3}$ and moves it to each other spin with probability $\tfrac{1-\lambda}{3}$. The spin score is $\sigma(0)=2$, $\sigma(1)=\sigma(2)=-1$. Depth-$0$ observations are spins, and depth-$(\ell+1)$ observations are finite multisets of depth-$\ell$ observations. For an offspring law $\mu$ on $\mathbb{N}$, $\mathcal L_\ell(i)$ is the law of the depth-$\ell$ observation with root spin $i$. $\mathcal L_0(i)$ is the point mass at $i$. To sample $\mathcal L_{\ell+1}(i)$, draw $K\sim\mu$, then $K$ independent pairs (child spin $j\sim M_\lambda(i,\cdot)$, observation from $\mathcal L_\ell(j)$), and record the multiset of the observations.
--
--   Ordered Galton–Watson observations are defined as follows. A depth-$0$ ordered observation is a spin. A depth-$(\ell+1)$ ordered observation is a pair $(n,v)$ of a child count $n$ and an $n$-tuple $v$ of depth-$\ell$ ordered observations. Under the ordered law $\mathcal O_\ell(i)$ with offspring law $\rho$: $\mathcal O_0(i)$ is the point mass at $i$. To sample $\mathcal O_{\ell+1}(i)$, draw $n\sim\rho$ and then $n$ independent copies of "$j\sim M_\lambda(i,\cdot)$, then $\mathcal O_\ell(j)$". Let $\phi_\ell$ forget the order recursively, sending $(n,v)$ to the multiset $\{\phi(v_0),\dots,\phi(v_{n-1})\}$. Then for every offspring law $\rho$, admissible $\lambda$, depth $\ell$ and root spin $i$,
--   $$
--   \mathcal O_\ell(i)\circ\phi_\ell^{-1}=\mathcal L_\ell(i)\quad\text{with offspring law }\mu=\rho .
--   $$
--
--   Moment computations can therefore be done in the ordered model, which has a product structure, and transferred to the multiset observations in which reconstruction is defined.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThreeStateClauses/OffspringLaws.lean#L46-L62

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

open OAI OAI.ThreeState OAI.ThreeState.TreeClauses OAI.ThreeState.TreeClauses.Tree
open scoped BigOperators ENNReal NNReal Topology
open Filter
open Set MeasureTheory
open scoped BigOperators ENNReal
open ThreeState.TreeClauses.Experiment ThreeState.TreeClauses.Radial

theorem OAI.ThreeState.TreeClauses.Tree.orderedLaw_forget (ρ : PMF ℕ) (lam : ℝ) (hlam : Admissible lam) (ℓ : ℕ) (i : Spin) :
    (orderedLaw ρ lam hlam ℓ i).map (forgetOrdered ℓ) = observationLaw lam hlam ρ ℓ i := by sorry
