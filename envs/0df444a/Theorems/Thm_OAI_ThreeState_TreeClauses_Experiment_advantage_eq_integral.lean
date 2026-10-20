-- Prove2me | Theorems.Thm_OAI_ThreeState_TreeClauses_Experiment_advantage_eq_integral
-- name    : OAI.ThreeState.TreeClauses.Experiment.advantage_eq_integral
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T20:08:27.032391+00:00
-- url     : https://prove2.me/theorems/47c3f9ab-2437-47ec-bf85-10f79989ac0d
-- title:
--   The reconstruction advantage is the mean total variation of the posterior message
-- statement:
--   Spins are elements of $\{0,1,2\}$, and $\lambda$ is admissible if $-\tfrac12\le\lambda\le1$. The channel $M_\lambda(i,\cdot)$ keeps the spin with probability $\tfrac{1+2\lambda}{3}$ and moves it to each other spin with probability $\tfrac{1-\lambda}{3}$. The spin score is $\sigma(0)=2$, $\sigma(1)=\sigma(2)=-1$. Depth-$0$ observations are spins, and depth-$(\ell+1)$ observations are finite multisets of depth-$\ell$ observations. For an offspring law $\mu$ on $\mathbb{N}$, $\mathcal L_\ell(i)$ is the law of the depth-$\ell$ observation with root spin $i$. $\mathcal L_0(i)$ is the point mass at $i$. To sample $\mathcal L_{\ell+1}(i)$, draw $K\sim\mu$, then $K$ independent pairs (child spin $j\sim M_\lambda(i,\cdot)$, observation from $\mathcal L_\ell(j)$), and record the multiset of the observations. With a uniform prior on the root spin, the posterior $\pi_\ell(o,\cdot)$ of the root given an observation $o$ is computed from the joint weights $\tfrac13\mathcal L_\ell(i)(o)$. The advantage is
--   $$
--   \mathrm{Adv}_\ell=\sum_o\bar{\mathcal L}_\ell(o)\cdot\frac12\sum_{i}\Bigl|\pi_\ell(o,i)-\frac13\Bigr|,\qquad \bar{\mathcal L}_\ell=\tfrac13\textstyle\sum_i\mathcal L_\ell(i).
--   $$
--   For an observation $o$, let $m(o)\in\mathbb{R}^3$ be the posterior message, with $m_i(o)=3\pi_\ell(o,i)$ (or $(1,1,1)$ if $o$ has marginal probability $0$). Let $\nu_\ell$ be the law of $m(o)$ when $o\sim\bar{\mathcal L}_\ell$, a probability measure on the compact message set. Write $\mathrm{tv}(m)=\frac16\sum_i|m_i-1|$. Then for every admissible $\lambda$, every offspring law and every depth $\ell$,
--   $$
--   \mathrm{Adv}_\ell=\int\mathrm{tv}(m)\,d\nu_\ell(m).
--   $$
--
--   This expresses the advantage as the integral of a fixed bounded continuous function against the law of the posterior message. Comparison and limit arguments can therefore be carried out at the level of message laws.
--
--   **Formalization Note** $\nu_\ell$ is `discreteProbability (observationLaw lam hlam offspring ℓ)`, and $\mathrm{tv}$ is `tvMessage`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThreeStateClauses/CompactLimits.lean#L407-L421

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

open OAI OAI.ThreeState OAI.ThreeState.TreeClauses OAI.ThreeState.TreeClauses.Experiment
open scoped BigOperators ENNReal NNReal Topology
open Filter
open Set MeasureTheory
open scoped BigOperators ENNReal
open ThreeState.TreeClauses.Radial

theorem OAI.ThreeState.TreeClauses.Experiment.advantage_eq_integral (lam : ℝ) (hlam : Admissible lam) (offspring : PMF ℕ) (ℓ : ℕ) :
    advantage lam hlam offspring ℓ =
      ∫ m, tvMessage m ∂(discreteProbability (observationLaw lam hlam offspring ℓ)).toMeasure := by sorry
