-- Prove2me | Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_adaptive_rank_completion
-- name    : OAI.LeanBlast.SecondKahnKalai.adaptive_rank_completion
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:53:03.756226+00:00
-- url     : https://prove2.me/theorems/b02efdd3-419a-4e8b-b45d-c810e2865080
-- title:
--   Adaptive completion: progress probability $3/4$ in every state finishes rank $s$ within $4s$ draws with probability at least $2/3$
-- statement:
--   Let $\Omega$ be a finite set and let $\mu$ be a probability law on $\Omega$, given by weights $\mu(\omega)\ge 0$ with $\sum_{\omega\in\Omega}\mu(\omega)=1$; for an event $E\subseteq\Omega$ write $\mu(E)=\sum_{\omega\in E}\mu(\omega)$, and for $f:\Omega\to\mathbb{R}$ write $\mathbb{E}_\mu[f]=\sum_{\omega\in\Omega}\mu(\omega)f(\omega)$. For $N\in\mathbb{N}$, $\mu^{\otimes N}$ denotes the product law on $\Omega^N$, with weight $\mu^{\otimes N}(\omega_0,\dots,\omega_{N-1})=\prod_{i<N}\mu(\omega_i)$; it describes $N$ independent draws with common law $\mu$.
--
--   Let $S$ be an arbitrary set of states, $\phi:S\times\Omega\to S$ an update map and $r:S\to\mathbb{N}$ a rank. For an initial state $x_0$ and draws $\omega=(\omega_0,\dots,\omega_{N-1})\in\Omega^N$ let $x_N(x_0,\omega)$ be the final state of the trajectory $x_{i+1}=\phi(x_i,\omega_i)$. Assume:
--
--   1. the rank never increases: $r(\phi(x,\omega))\le r(x)$ for all $x\in S$, $\omega\in\Omega$;
--   2. in every unfinished state one fresh draw makes progress with probability at least $3/4$: for every $x\in S$ with $r(x)\neq0$,
--   $\mu\bigl(\{\omega\in\Omega: r(\phi(x,\omega))<r(x)\}\bigr)\ge \tfrac34$.
--
--   **Theorem.** For every $s\in\mathbb{N}$ and every initial state $x_0$ with $r(x_0)\le s$,
--   $$
--   \mu^{\otimes 4s}\Bigl(\bigl\{\omega\in\Omega^{4s}:\ r\bigl(x_{4s}(x_0,\omega)\bigr)=0\bigr\}\Bigr)\ \ge\ \frac23 .
--   $$
--
--   The probability of progress may depend arbitrarily on the current state, and hence on all earlier draws; only the fresh draws are independent. The case $s=0$ is included (then no draws are made and $r(x_0)=0$ already). Such a bound is used for multi-round random procedures in which each round draws a fresh independent random object and a successful round strictly decreases a rank measuring the remaining work: with probability at least $2/3$ the work is finished after $4s$ rounds.
--
--   **Formalization Note** The product law is `μ.iid (4 * s)` on `Fin (4 * s) → Ω` and the final state is `adaptiveRun step (4 * s) initial draws`. No finiteness or other structure is required of the state type.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GraphThreshold/AdaptiveTrials.lean#L183-L223

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

theorem OAI.LeanBlast.SecondKahnKalai.adaptive_rank_completion [Fintype Ω] (μ : FiniteLaw Ω)
    (rank : State → ℕ) (step : State → Ω → State)
    (hstep : ∀ state draw, rank (step state draw) ≤ rank state)
    (hprogress : ∀ state, rank state ≠ 0 →
      (3 / 4 : ℝ) ≤ μ.prob (fun draw => rank (step state draw) < rank state))
    (s : ℕ) (initial : State) (hinitial : rank initial ≤ s) :
    (2 / 3 : ℝ) ≤ (μ.iid (4 * s)).prob
      (fun draws => rank (adaptiveRun step (4 * s) initial draws) = 0) := by sorry
