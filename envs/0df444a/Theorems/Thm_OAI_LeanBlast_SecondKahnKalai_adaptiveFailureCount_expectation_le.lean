-- Prove2me | Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_adaptiveFailureCount_expectation_le
-- name    : OAI.LeanBlast.SecondKahnKalai.adaptiveFailureCount_expectation_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:51:38.220914+00:00
-- url     : https://prove2.me/theorems/1451fb56-ff8d-4ef2-ac50-80b2ef0c6288
-- title:
--   Adaptive trials with fresh i.i.d. draws: expected number of failures is at most $nq$
-- statement:
--   Let $\Omega$ be a finite set and let $\mu$ be a probability law on $\Omega$, given by weights $\mu(\omega)\ge 0$ with $\sum_{\omega\in\Omega}\mu(\omega)=1$; for an event $E\subseteq\Omega$ write $\mu(E)=\sum_{\omega\in E}\mu(\omega)$, and for $f:\Omega\to\mathbb{R}$ write $\mathbb{E}_\mu[f]=\sum_{\omega\in\Omega}\mu(\omega)f(\omega)$. For $N\in\mathbb{N}$, $\mu^{\otimes N}$ denotes the product law on $\Omega^N$, with weight $\mu^{\otimes N}(\omega_0,\dots,\omega_{N-1})=\prod_{i<N}\mu(\omega_i)$; it describes $N$ independent draws with common law $\mu$.
--
--   Let $S$ be an arbitrary set of *states*, let $\phi:S\times\Omega\to S$ be an update map, and let $\beta:S\times\Omega\to\{\mathrm{true},\mathrm{false}\}$ be a *failure* predicate. For an initial state $x_0\in S$ and draws $\omega=(\omega_0,\dots,\omega_{n-1})\in\Omega^n$, the adaptive trajectory is $x_{i+1}=\phi(x_i,\omega_i)$ for $0\le i<n$, and the number of failures along it is $N_n(x_0,\omega)=\#\{\,0\le i<n:\beta(x_i,\omega_i)=\mathrm{true}\,\}$.
--
--   **Theorem.** Let $q\in\mathbb{R}$ and assume that, from every state, one fresh draw fails with probability at most $q$:
--   $$
--   \mu\bigl(\{\omega\in\Omega:\beta(x,\omega)=\mathrm{true}\}\bigr)\le q\qquad\text{for every }x\in S.
--   $$
--   Then for every $n\in\mathbb{N}$ and every initial state $x_0\in S$,
--   $$
--   \mathbb{E}_{\mu^{\otimes n}}\bigl[N_n(x_0,\cdot)\bigr]=\sum_{\omega\in\Omega^n}\mu^{\otimes n}(\omega)\,N_n(x_0,\omega)\ \le\ n\,q .
--   $$
--
--   Whether the $i$-th attempt fails may depend on the whole history through the current state $x_i$; only the draws themselves are independent, and no independence between the failure indicators is assumed. This is the expectation estimate behind completion bounds for adaptive procedures: combined with Markov's inequality it shows that a process which makes progress with probability at least $3/4$ in every unfinished state completes within a linear number of rounds with probability at least $2/3$.
--
--   **Formalization Note** The law is a `FiniteLaw Ω`, the product law is `μ.iid n` on `Fin n → Ω`, the predicate $\beta$ is Boolean-valued, and $N_n$ is `adaptiveFailureCount step bad n initial`, a natural number cast to $\mathbb{R}$. No finiteness or other structure is required of the state type.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GraphThreshold/AdaptiveTrials.lean#L74-L110

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

theorem OAI.LeanBlast.SecondKahnKalai.adaptiveFailureCount_expectation_le [Fintype Ω]
    (μ : FiniteLaw Ω) (step : State → Ω → State) (bad : State → Ω → Bool)
    (q : ℝ) (hbad : ∀ state, μ.prob (fun draw => bad state draw = true) ≤ q)
    (n : ℕ) (initial : State) :
    (μ.iid n).expectation (fun draws => (adaptiveFailureCount step bad n initial draws : ℝ)) ≤
      (n : ℝ) * q := by sorry
