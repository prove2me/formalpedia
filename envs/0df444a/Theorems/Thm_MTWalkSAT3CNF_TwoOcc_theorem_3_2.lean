-- Prove2me | Theorems.Thm_MTWalkSAT3CNF_TwoOcc_theorem_3_2
-- name    : MTWalkSAT3CNF.TwoOcc.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:27:26.120474+00:00
-- url     : https://prove2.me/theorems/b074c101-aec5-44e3-9be5-e8dacb6baf81
-- title:
--   Theorem 3.2 (Pegden) — algorithmic cluster-expansion local lemma
-- statement:
--   Let $V$ be a finite set of mutually independent variables ($x_v$ with law $\nu_v$ on a measurable space) and let $(A_i)_{i\in I}$ be a finite family of measurable events, $A_i$ determined by the variables in $\mathrm{vbl}(i)$. Let $G$ be the dependency graph (distinct events adjacent when they share a variable) and $\bar\Gamma(i)$ the event $i$ together with its neighbours. Suppose there are real numbers $\mu_i>0$ with
--
--   $$\mathbb P(A_i)\le\frac{\mu_i}{\displaystyle\sum_{J\subseteq\bar\Gamma(i),\ J\text{ independent}}\ \prod_{j\in J}\mu_j}\qquad\text{for every } i\in I .$$
--
--   Then for every adaptive rule that selects a currently occurring event:
--
--   1. the Moser–Tardos algorithm terminates almost surely;
--   2. $\mathbb E[N_i]\le\mu_i$ for every $i$, where $N_i$ is the number of times event $i$ is resampled;
--   3. $\mathbb E[T_{MT}]\le\sum_{i\in I}\mu_i$.
--
--   This is the imported result [Peg14, Theorem 1.4] that the paper applies to bound Moser–Tardos on 3-CNF formulas with $\Delta(F)\le2$ (Theorem 3.1).
--
--   Differences from the source:
--   - generalization: a finite family of events → events indexed by a finite type I (two indices may carry the same set); reason: a family is the case of distinct indices; Theorem 3.1 needs indexing because repeated clauses give equal bad events
--   - generalization: events depend on variables and are adjacent if they depend on a common variable → each event comes with a set vbl i of variables determining it, which the algorithm resamples; adjacency is overlap of these sets; reason: the minimal determining set exists on a product space and recovers the paper's graph G and algorithm; other determining sets give further instances of the standard variable-setting framework
--   - reading: any rule that selects a currently occurring bad event → a family of Markov kernels from the history (all past states and past choices) to a choice, selecting an occurring event almost surely, possibly randomized; reason: the rule must be measurable in the history for the process to have a law on general value spaces; deterministic measurable rules are the Dirac case
--   - encoding: mutually independent variables → values in arbitrary measurable spaces with probability laws, joint law Measure.pi; reason: Lean convention; same instances
--   - encoding: terminates almost surely; E[N_A]; E[T_MT] → ∀ᵐ ω, T_MT ω ≠ ⊤; N_i the cardinality (ℕ∞) of the set of steps choosing i; expectations as lintegral in ℝ≥0∞, bounds ENNReal.ofReal μ_i and ENNReal.ofReal Σ μ_i; reason: Lean convention; same quantities
-- source:
--   Minbo Gao, Kun He, Tao Jiang, Tight Variable-Occurrence Bounds and Exponential Separations for Moser–Tardos and WalkSAT on 3-CNF, STOC 2027 submission #914 (October 2026), Theorem 3.2 (= [Peg14, Theorem 1.4]), p. 11. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/914.pdf

import Definitions.Def_MTWalkSAT3CNF_TwoOcc_MoserTardos

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MTWalkSAT3CNF.TwoOcc

/-- Theorem 3.2 ([Peg14, Theorem 1.4]), p. 11: the algorithmic cluster-expansion local lemma.
If `P(A_i) ≤ μ_i / Σ_{J ⊆ Γ̄(A_i) independent} Π_{j ∈ J} μ_j` with `μ_i > 0` for every event, then
under every adaptive rule selecting an occurring event, Moser–Tardos terminates almost surely,
`E[N_i] ≤ μ_i` for every event, and `E[T_MT] ≤ Σ_i μ_i`. -/
theorem theorem_3_2 {V : Type*} [Fintype V] [DecidableEq V] {X : V → Type*}
    [∀ v, MeasurableSpace (X v)] {I : Type*} [Fintype I] [DecidableEq I]
    (E : EventSystem V X I) (μ : I → ℝ) (hμ : ∀ i, 0 < μ i)
    (hcrit : ∀ i, E.prob i ≤ μ i / E.clusterSum μ i) (R : MTRule E) :
    (∀ᵐ ω ∂(E.mtLaw R), E.mtTimeOf ω ≠ ⊤) ∧
    (∀ i, E.expectedResamples R i ≤ ENNReal.ofReal (μ i)) ∧
    E.expectedTime R ≤ ENNReal.ofReal (∑ i, μ i) := by sorry

end MTWalkSAT3CNF.TwoOcc
