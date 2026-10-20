-- Prove2me | Theorems.Thm_OAI_ThreeState_TreeClauses_Experiment_discrete_degradation_centered
-- name    : OAI.ThreeState.TreeClauses.Experiment.discrete_degradation_centered
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T20:03:01.232169+00:00
-- url     : https://prove2.me/theorems/775751cc-8cdd-4fe8-b9d0-d86200f39135
-- title:
--   The posterior after degradation is the conditional expectation of the posterior before it
-- statement:
--   Let $\alpha,\beta$ be countable types with measurable singletons. Let $p=(p_0,p_1,p_2)$ be three discrete laws on $\alpha$, and $K$ a Markov kernel from $\alpha$ to $\beta$. For laws $q=(q_0,q_1,q_2)$ on a type and an observation $x$, let $m^q(x)$ be the posterior message: the vector with coordinates $q_i(x)/w(x)$, where $w(x)=\frac13\sum_jq_j(x)$, and $(1,1,1)$ if $w(x)=0$. Let $\bar p=\frac13\sum_ip_i$, and let $P$ be the joint law of $(a,b)$ with $a\sim\bar p$ and $b\sim K(a)$. Write $p\gg\!=K$ for the three degraded laws $\bigl(p_j\gg\!=K\bigr)_j$ on $\beta$.
--
--   Then for every spin $i$ and every bounded $g:\beta\to\mathbb{R}$ ($|g|\le C$),
--   $$
--   \int\Bigl(m^{p}_i(a)-m^{p\gg=K}_i(b)\Bigr)\,g(b)\,dP(a,b)=0 .
--   $$
--
--   In other words, $m^{p\gg=K}_i(b)$ is the conditional expectation of $m^p_i(a)$ given $b$. The posterior computed from the degraded observation is an average of the posterior computed from the original one. This is the martingale structure behind the monotonicity and convergence of reconstruction quantities.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThreeStateClauses/Degradation.lean#L76-L90

import Mathlib
import Definitions.Def_ThreeStateTreeClauses
import Definitions.Def_OAI_Probability_ThreeStateClauses_RadialAlgebra
import Definitions.Def_OAI_Probability_ThreeStateClauses_PosteriorLaw
import Definitions.Def_OAI_Probability_ThreeStateClauses_DiscreteLaw
import Definitions.Def_OAI_Probability_ThreeStateClauses_Products
import Definitions.Def_OAI_Probability_ThreeStateClauses_Degradation

open OAI OAI.ThreeState OAI.ThreeState.TreeClauses OAI.ThreeState.TreeClauses.Experiment
open scoped BigOperators ENNReal NNReal Topology
open Filter
open Set MeasureTheory
open scoped BigOperators ENNReal
open ThreeState.TreeClauses.Radial
variable {α β : Type*}
variable [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Countable β] [MeasurableSpace β] [MeasurableSingletonClass β]

theorem OAI.ThreeState.TreeClauses.Experiment.discrete_degradation_centered (p : Fin 3 → PMF α) (K : α → PMF β) (i : Fin 3)
    {g : β → ℝ} {C : ℝ} (hg : ∀ b, |g b| ≤ C) :
    (∫ z, ((discreteMessage p z.1).1 i-(discreteMessage (fun j ↦ (p j).bind K) z.2).1 i)*g z.2
      ∂(kernelJoint (discreteMarginal p) K).toMeasure) = 0 := by sorry
