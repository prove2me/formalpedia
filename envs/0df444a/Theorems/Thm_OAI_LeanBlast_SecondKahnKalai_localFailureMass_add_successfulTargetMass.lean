-- Prove2me | Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_localFailureMass_add_successfulTargetMass
-- name    : OAI.LeanBlast.SecondKahnKalai.localFailureMass_add_successfulTargetMass
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:59:49.94001+00:00
-- url     : https://prove2.me/theorems/5dde2297-0ff6-4ebf-a758-07b9b6aba3d1
-- title:
--   Local failure mass plus total successful target mass of a resampling step equals one
-- statement:
--   Let $X$ be a set.
--
--   **Resampling quantities.** Let $B$ be a finite index set with a probability law $\mu$ (weights $\mu(b)\ge0$, $\sum_b\mu(b)=1$), let $A=(A_b)_{b\in B}$ be finite labels $A_b\subseteq X$, let $\rho>0$, let $W\subseteq X$ be finite and let $M\in\mathbb{N}$. Put
--   $$
--   Z(Y)=\sum_{b\in B:\ A_b\subseteq Y}\mu(b)\,\rho^{-|A_b|},\qquad
--   \pi(c,b)=\mu(c)\cdot\frac{\mathbf 1[A_b\subseteq W\cup A_c]\;\mu(b)\,\rho^{-|A_b|}}{Z(W\cup A_c)}\qquad(c,b\in B).
--   $$
--   So $\pi$ describes a *source* $c$ drawn from $\mu$ followed by a *target* $b$ chosen among the indices whose label lies in $W\cup A_c$, with probability proportional to $\mu(b)\rho^{-|A_b|}$. A pair $(c,b)$ is a *local success* $S_M(c,b)$ if $Z(W\cup A_c)\ge e^{-10M}$ and $|A_b\setminus W|\le\lfloor M/2\rfloor$, and a *local failure* otherwise. The *successful target mass* of $b$ is $s_M(b)=\sum_{c\in B:\ S_M(c,b)}\pi(c,b)$.
--
--   The *local failure mass* is $\displaystyle\sum_{b\in B}\ \sum_{c\in B:\ \neg S_M(c,b)}\pi(c,b)$.
--
--   **Theorem.** Assume that every weight of $\mu$ is strictly positive, $\mu(b)>0$ for all $b\in B$, and that $\rho>0$. Then for every $M\in\mathbb{N}$ and every finite $W\subseteq X$,
--   $$
--   \sum_{b\in B}\ \sum_{c\in B:\ \neg S_M(c,b)}\pi(c,b)\;+\;\sum_{b\in B}s_M(b)\;=\;1 .
--   $$
--
--   Since local success and local failure are complementary, the identity says that the source–target weights $\pi$ have total mass one, so the failure mass and the successful target masses form a partition of a probability distribution. It is used in the analysis of a recursive bad-node potential for tree reduction, where a lower bound on the successful target mass of good children is turned into an upper bound on the remaining (failure or bad-child) mass.
--
--   **Formalization Note** The two masses are `localFailureMass μ A ρ m W` and `successfulTargetMass μ A ρ m W b`, built from `resamplingWeight μ A ρ W (c, b)`, which is $\pi(c,b)$; the law is a `FiniteLaw B` and the positivity hypothesis is `μ.IsPositive`; $X$ has decidable equality and labels are `Finset X`. The positivity assumptions ensure that every denominator $Z(W\cup A_c)$ is nonzero; without them Lean's convention $x/0=0$ would apply.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GraphThreshold/TreeReductionData.lean#L46-L64

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.List.Pairwise
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.Monotone
import Definitions.Def_SecondKahnKalai
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphEncoding
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphProbability
import Definitions.Def_OAI_Combinatorics_GraphThreshold_EmbeddingExtension
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphSupport
import Definitions.Def_OAI_Combinatorics_GraphThreshold_Basic
import Definitions.Def_OAI_Combinatorics_GraphThreshold_FiniteProbability
import Definitions.Def_OAI_Combinatorics_GraphThreshold_CopyOrbits
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphExpectedCopies
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphCopies
import Definitions.Def_OAI_Combinatorics_GraphThreshold_ProbabilityTree
import Definitions.Def_OAI_Combinatorics_GraphThreshold_LocalFailureNumerics
import Definitions.Def_OAI_Combinatorics_GraphThreshold_Predecessor
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphHierarchy
import Definitions.Def_OAI_Combinatorics_GraphThreshold_BernoulliCoupling
import Definitions.Def_OAI_Combinatorics_GraphThreshold_AdaptiveTrials
import Definitions.Def_OAI_Combinatorics_GraphThreshold_ProbabilityTreeFacts
import Definitions.Def_OAI_Combinatorics_GraphThreshold_ProbabilityTreeTrim
import Definitions.Def_OAI_Combinatorics_GraphThreshold_CapacityIteration
import Definitions.Def_OAI_Combinatorics_GraphThreshold_Resampling
import Definitions.Def_OAI_Combinatorics_GraphThreshold_ResamplingEvents
import Definitions.Def_OAI_Combinatorics_GraphThreshold_TreeReductionData

open OAI OAI.LeanBlast OAI.LeanBlast.SecondKahnKalai
open scoped BigOperators
open Classical
variable {X B : Type*} [DecidableEq X] [Fintype B]

theorem OAI.LeanBlast.SecondKahnKalai.localFailureMass_add_successfulTargetMass (μ : FiniteLaw B)
    (A : B → Finset X) {ρ : ℝ} (hμ : μ.IsPositive) (hρ : 0 < ρ)
    (m : ℕ) (W : Finset X) :
    localFailureMass μ A ρ m W + ∑ b, successfulTargetMass μ A ρ m W b = 1 := by sorry
