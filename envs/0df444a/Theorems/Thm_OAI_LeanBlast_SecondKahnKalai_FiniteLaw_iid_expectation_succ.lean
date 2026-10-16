-- Prove2me | Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_FiniteLaw_iid_expectation_succ
-- name    : OAI.LeanBlast.SecondKahnKalai.FiniteLaw.iid_expectation_succ
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:51:08.436252+00:00
-- url     : https://prove2.me/theorems/286524c9-8c00-4a12-89fa-efa9170e0e69
-- title:
--   Expectation over $n+1$ i.i.d. draws as an iterated expectation over the first draw and the remaining $n$
-- statement:
--   Let $\Omega$ be a finite set and $\mu$ a probability distribution on $\Omega$, given by weights $\mu(\omega)\ge 0$ with $\sum_{\omega\in\Omega}\mu(\omega)=1$; write $\mathbb{E}_{\mu}[g]=\sum_{\omega}\mu(\omega)g(\omega)$. For $n\in\mathbb{N}$ let $\mu^{\otimes n}$ be the law of $n$ independent draws from $\mu$, i.e. the distribution on sequences $(\omega_0,\dots,\omega_{n-1})\in\Omega^{n}$ with weight $\prod_{i<n}\mu(\omega_i)$.
--
--   **Theorem.** For every $n\in\mathbb{N}$ and every function $f:\Omega^{n+1}\to\mathbb{R}$,
--   $$
--   \mathbb{E}_{\mu^{\otimes(n+1)}}[f]=\mathbb{E}_{\omega_0\sim\mu}\Bigl[\mathbb{E}_{(\omega_1,\dots,\omega_n)\sim\mu^{\otimes n}}\bigl[f(\omega_0,\omega_1,\dots,\omega_n)\bigr]\Bigr].
--   $$
--
--   This is the finite Fubini, or conditional-expectation, identity for a fresh independent draw: given the first draw, the remaining draws are again independent with law $\mu$. It is the induction step for analysing adaptive sequences of independent trials, in which a state is updated after each draw.
--
--   **Formalization Note** A law is the structure `FiniteLaw Ω` (nonnegative weights summing to $1$) and $\mu^{\otimes n}$ is `μ.iid n`, a law on functions `Fin n → Ω`. The sequence $(\omega_0,\omega_1,\dots,\omega_n)$ obtained by prepending the first draw to the remaining ones is `Fin.cases head tail`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GraphThreshold/AdaptiveTrials.lean#L40-L56

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

open OAI OAI.LeanBlast OAI.LeanBlast.SecondKahnKalai OAI.LeanBlast.SecondKahnKalai.FiniteLaw
open scoped BigOperators
universe u v
variable {State : Type u} {Ω : Type v}
variable [Fintype Ω]

theorem OAI.LeanBlast.SecondKahnKalai.FiniteLaw.iid_expectation_succ (μ : FiniteLaw Ω) (n : ℕ)
    (f : (Fin (n + 1) → Ω) → ℝ) :
    (μ.iid (n + 1)).expectation f =
      μ.expectation (fun head => (μ.iid n).expectation (fun tail => f (Fin.cases head tail))) := by sorry
