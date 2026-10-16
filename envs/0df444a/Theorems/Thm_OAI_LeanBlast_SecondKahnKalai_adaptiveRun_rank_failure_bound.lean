-- Prove2me | Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_adaptiveRun_rank_failure_bound
-- name    : OAI.LeanBlast.SecondKahnKalai.adaptiveRun_rank_failure_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:52:05.756302+00:00
-- url     : https://prove2.me/theorems/e94e5972-61e2-4f1b-9f3b-e935b88284d2
-- title:
--   Rank accounting on an unfinished adaptive trajectory: $n+r(x_n)\le r(x_0)+\#\{\text{failed steps}\}$
-- statement:
--   Let $S$ be a set of states, $\Omega$ a set of possible draws, $\phi:S\times\Omega\to S$ an update map, and $r:S\to\mathbb{N}$ a *rank* that never increases under an update:
--   $$
--   r(\phi(x,\omega))\le r(x)\qquad\text{for all }x\in S,\ \omega\in\Omega .
--   $$
--   Given an initial state $x_0$, a length $n\in\mathbb{N}$ and draws $\omega_0,\dots,\omega_{n-1}\in\Omega$, define the trajectory $x_{i+1}=\phi(x_i,\omega_i)$ for $0\le i<n$. Step $i$ is called a *failure* if $r(x_i)\neq 0$ and $r(x_{i+1})$ is not strictly smaller than $r(x_i)$; thus once the rank has reached $0$, no further step counts as a failure. Let $F_n$ be the number of failures among the steps $0,1,\dots,n-1$.
--
--   **Theorem.** If the final rank is still positive, $r(x_n)\neq 0$, then
--   $$
--   n+r(x_n)\ \le\ r(x_0)+F_n .
--   $$
--
--   In words: on a trajectory that has not finished, every step that is not a failure consumes at least one unit of rank, and the rank that is left at the end is accounted for as well. For example, with $n=4s$ steps and $r(x_0)\le s$, an unfinished trajectory must contain at least $3s+1$ failures; this deterministic count is what a Markov-inequality argument turns into a completion probability for adaptive random processes.
--
--   **Formalization Note** The statement is purely deterministic: no probability law and no finiteness assumption appear. The final state is `adaptiveRun step n initial draws` with `draws : Fin n → Ω`, the failure predicate is the Boolean function `rankFailure rank step`, and $F_n$ is `adaptiveFailureCount step (rankFailure rank step) n initial draws`; all quantities are natural numbers.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GraphThreshold/AdaptiveTrials.lean#L127-L156

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

open OAI OAI.LeanBlast OAI.LeanBlast.SecondKahnKalai
open scoped BigOperators
universe u v
variable {State : Type u} {Ω : Type v}

theorem OAI.LeanBlast.SecondKahnKalai.adaptiveRun_rank_failure_bound (rank : State → ℕ) (step : State → Ω → State)
    (hstep : ∀ state draw, rank (step state draw) ≤ rank state)
    (n : ℕ) (initial : State) (draws : Fin n → Ω)
    (hincomplete : rank (adaptiveRun step n initial draws) ≠ 0) :
    n + rank (adaptiveRun step n initial draws) ≤
      rank initial + adaptiveFailureCount step (rankFailure rank step) n initial draws := by sorry
