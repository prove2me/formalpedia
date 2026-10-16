-- Prove2me | Theorems.Thm_OAI_RandomKSAT_insertion_moments
-- name    : OAI.RandomKSAT.insertion_moments
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T18:26:13.226963+00:00
-- url     : https://prove2.me/theorems/a924448e-ebca-43e3-bbbf-c2e7c4cf3e72
-- title:
--   Mean and variance of the shift $t+\mathbf 1[i<t]$ for a uniform position $i$
-- statement:
--   Let $L$ and $t$ be natural numbers with $L\ge1$ and $t\le L$, let $i$ be uniformly distributed on $\{0,1,\dots,L-1\}$, and consider the random variable
--   $$
--   X=t+\mathbf 1[i<t].
--   $$
--
--   **Theorem.** The mean and the variance of $X$ are as follows.
--
--   1. The mean is
--   $$
--   \mathbb E[X]=\Big(1+\frac1L\Big)\,t .
--   $$
--   2. The variance is
--   $$
--   \operatorname{Var}(X)=\mathbb E[X^2]-\mathbb E[X]^2=\frac{t\,(L-t)}{L^2}.
--   $$
--
--   Equivalently, $X-t$ is a Bernoulli variable with parameter $t/L$. Applied with $L$ the number of insertion slots of a list $r$ (that is, its length plus one) and $t$ its failure time, this gives the conditional mean and variance of the failure time after a harmless clause is inserted at a uniformly random position.
--
--   **Formalization Note** Both moments are uniform averages over `i : Fin L`: the mean is `favg` and the variance is `fvariance`, defined as the average of the square minus the square of the average. The value $X$ is computed in $\mathbb N$ and then cast to $\mathbb R$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/InsertionVariance.lean#L195-L214

import Mathlib
import Definitions.Def_SATVariance
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_BlockKilling
import Definitions.Def_OAI_Probability_SATVariance_MarkovReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FiniteVariance
import Definitions.Def_OAI_Probability_SATVariance_LifetimePotential
import Definitions.Def_OAI_Probability_SATVariance_RootDisintegration__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FiberRefresh
import Definitions.Def_OAI_Probability_SATVariance_PairEvolution
import Definitions.Def_OAI_Probability_SATVariance_HiddenTests
import Definitions.Def_OAI_Probability_SATVariance_WeightedRewards
import Definitions.Def_OAI_Probability_SATVariance_CountMoments
import Definitions.Def_OAI_Probability_SATVariance_SupportProbabilities__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_OmissionCompression
import Definitions.Def_OAI_Probability_SATVariance_CapBridge
import Definitions.Def_OAI_Probability_SATVariance_ShuffleAverages
import Definitions.Def_OAI_Probability_SATVariance_BystanderStops
import Definitions.Def_OAI_Probability_SATVariance_InsertionVariance

open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

theorem OAI.RandomKSAT.insertion_moments {L t : ℕ} (hL : 0 < L) (ht : t ≤ L) :
    favg (fun i : Fin L => ((t + if i.val < t then 1 else 0 : ℕ):ℝ)) =
      (1+1/(L:ℝ))*t ∧
    fvariance (fun i : Fin L => ((t + if i.val < t then 1 else 0 : ℕ):ℝ)) =
      (t:ℝ)*((L:ℝ)-t)/(L:ℝ)^2 := by sorry
