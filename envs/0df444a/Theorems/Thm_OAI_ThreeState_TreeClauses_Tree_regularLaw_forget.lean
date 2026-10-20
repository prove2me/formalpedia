-- Prove2me | Theorems.Thm_OAI_ThreeState_TreeClauses_Tree_regularLaw_forget
-- name    : OAI.ThreeState.TreeClauses.Tree.regularLaw_forget
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T20:06:30.168484+00:00
-- url     : https://prove2.me/theorems/59d81868-3d29-4ca4-a33f-58c1f7939d30
-- title:
--   Forgetting child order in the $b$-ary broadcast tree gives the regular observation law
-- statement:
--   Spins are elements of $\{0,1,2\}$. A parameter $\lambda\in\mathbb{R}$ is admissible if $-\tfrac12\le\lambda\le1$; the channel $M_\lambda(i,\cdot)$ keeps the spin $i$ with probability $\tfrac{1+2\lambda}{3}$ and moves it to each other spin with probability $\tfrac{1-\lambda}{3}$. A depth-$0$ observation is a spin, and a depth-$(\ell+1)$ observation is a finite multiset of depth-$\ell$ observations. For an offspring law $\mu$ on $\mathbb{N}$, $\mathcal L_\ell(i)$ is the law of the depth-$\ell$ observation with root spin $i$. $\mathcal L_0(i)$ is the point mass at $i$. To sample $\mathcal L_{\ell+1}(i)$, draw $K\sim\mu$ and then $K$ independent pairs (child spin $j\sim M_\lambda(i,\cdot)$, observation from $\mathcal L_\ell(j)$), and record the multiset of the $K$ observations.
--
--   For $b\in\mathbb{N}$, let $\mathcal R_\ell(i)$ be the ordered $b$-ary law. It lives on ordered observations, where depth $\ell+1$ consists of $b$-tuples of depth-$\ell$ observations. $\mathcal R_0(i)$ is the point mass at $i$, and $\mathcal R_{\ell+1}(i)$ is the product of $b$ independent copies of "$j\sim M_\lambda(i,\cdot)$, then $\mathcal R_\ell(j)$". Let $\phi_\ell$ forget the order recursively, turning tuples into multisets. Then for every admissible $\lambda$, every $\ell$ and every root spin $i$,
--   $$
--   \mathcal R_\ell(i)\circ\phi_\ell^{-1}=\mathcal L_\ell(i)\quad\text{with offspring law }\mu=\delta_b .
--   $$
--
--   So the regular tree can be analysed through its ordered version, with finite state spaces and product structure, without changing the law of the unordered observation.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThreeStateClauses/RegularLaw.lean#L74-L87

import Mathlib
import Definitions.Def_ThreeStateTreeClauses
import Definitions.Def_OAI_Probability_ThreeStateClauses_RadialAlgebra
import Definitions.Def_OAI_Probability_ThreeStateClauses_PosteriorLaw
import Definitions.Def_OAI_Probability_ThreeStateClauses_DiscreteLaw
import Definitions.Def_OAI_Probability_ThreeStateClauses_Products
import Definitions.Def_OAI_Probability_ThreeStateClauses_Degradation
import Definitions.Def_OAI_Probability_ThreeStateClauses_RegularLaw

open OAI OAI.ThreeState OAI.ThreeState.TreeClauses OAI.ThreeState.TreeClauses.Tree
open scoped BigOperators ENNReal NNReal Topology
open Filter
open Set MeasureTheory
open scoped BigOperators ENNReal
open ThreeState.TreeClauses.Experiment

theorem OAI.ThreeState.TreeClauses.Tree.regularLaw_forget (b : ℕ) (lam : ℝ) (hlam : Admissible lam) (ℓ : ℕ) (i : Spin) :
    (regularLaw b lam hlam ℓ i).map (forgetRegular b ℓ) =
      observationLaw lam hlam (PMF.pure b) ℓ i := by sorry
