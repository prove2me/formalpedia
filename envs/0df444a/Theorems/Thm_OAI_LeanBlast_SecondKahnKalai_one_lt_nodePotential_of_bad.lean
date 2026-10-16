-- Prove2me | Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_one_lt_nodePotential_of_bad
-- name    : OAI.LeanBlast.SecondKahnKalai.one_lt_nodePotential_of_bad
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:10:48.767984+00:00
-- url     : https://prove2.me/theorems/666834fd-19ea-46da-85d3-064d0ea7d2ec
-- title:
--   A node with too little good mass has potential greater than one
-- statement:
--   Let $B$ be a finite index set and $m\in\mathbb{N}$. For a real number $\varphi$ and families $t=(t_b)_{b\in B}$, $\psi=(\psi_b)_{b\in B}$ of real numbers, define the node potential
--   $$
--   \Phi_m(\varphi,t,\psi)=\frac{\varphi+\sum_{b\in B}t_b\,\psi_b}{e^{-m}}=e^{m}\Big(\varphi+\sum_{b\in B}t_b\,\psi_b\Big).
--   $$
--   Let $G\subseteq B$ be any set of "good" indices and assume
--
--   1. $t_b\ge 0$ and $\psi_b\ge 0$ for every $b\in B$;
--   2. $\varphi+\sum_{b\in B}t_b=1$;
--   3. $\psi_b>1$ for every $b\notin G$;
--   4. $\sum_{b\in G}t_b<1-e^{-m}$.
--
--   Then
--   $$
--   \Phi_m(\varphi,t,\psi)>1 .
--   $$
--
--   In the tree-reduction argument, $\varphi$ is the local failure mass of a node, $t_b$ the successful transition mass into child $b$, $\psi_b$ the potential of the subtree at $b$, and $G$ the set of good children; a node is good when at least $1-e^{-m}$ of the mass goes successfully to good children. The lemma is the induction step showing that every bad node has potential greater than $1$, so that Markov's inequality applied to the potential bounds the probability of badness. No sign condition on $\varphi$ is needed, and children with $t_b=0$ need no special treatment.
--
--   **Formalization Note** $\Phi_m$ is `nodePotential m failure target childPotential`, defined as a division by `Real.exp (-(m : ℝ))`. The good set is a predicate `good : B → Prop`, and $\sum_{b\in G}t_b$ is written as a sum of `if good b then target b else 0`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GraphThreshold/TreePotential.lean#L40-L66

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
import Definitions.Def_OAI_Combinatorics_GraphThreshold_TreeReduction
import Definitions.Def_OAI_Combinatorics_GraphThreshold_OutsideChangeOfMeasure
import Definitions.Def_OAI_Combinatorics_GraphThreshold_TreePotential

open OAI OAI.LeanBlast OAI.LeanBlast.SecondKahnKalai
open scoped BigOperators
open Classical

theorem OAI.LeanBlast.SecondKahnKalai.one_lt_nodePotential_of_bad {B : Type*} [Fintype B]
    (m : ℕ) (failure : ℝ) (target childPotential : B → ℝ) (good : B → Prop)
    (ht : ∀ b, 0 ≤ target b) (hc : ∀ b, 0 ≤ childPotential b)
    (hmass : failure + ∑ b, target b = 1)
    (hchild : ∀ b, ¬good b → 1 < childPotential b)
    (hbad : (∑ b, if good b then target b else 0) < 1 - Real.exp (-(m : ℝ))) :
    1 < nodePotential m failure target childPotential := by sorry
