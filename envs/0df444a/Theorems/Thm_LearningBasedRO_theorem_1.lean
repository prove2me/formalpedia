-- Prove2me | Theorems.Thm_LearningBasedRO_theorem_1
-- name    : LearningBasedRO.theorem_1
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T13:31:04.227439+00:00
-- url     : https://prove2.me/theorems/25897af3-fa41-4a00-b594-40a9f3307391
-- title:
--   Theorem 1 (Basic statistical guarantee) — with $n_2\ge\log\delta/\log(1-\epsilon)$, $U(D)$ satisfies (3) and RO solutions are CCP-feasible with confidence $1-\delta$
-- statement:
--   Let $P$ be a probability distribution of the random parameter $\xi$ on a measurable space $E$ (the paper: $\mathbb R^m$), and let $0<\epsilon<1$, $0<\delta<1$. Let $D$ be an i.i.d. sample from $P$, partitioned into $D_1=(\xi^1_1,\dots,\xi^1_{n_1})$ and $D_2=(\xi^2_1,\dots,\xi^2_{n_2})$, where $n_1\ge 0$ and
--   $$n_2\ \ge\ \frac{\log\delta}{\log(1-\epsilon)} .$$
--   Let $t(D_1,\cdot):E\to\mathbb R$ be a score map constructed from $D_1$ (jointly measurable in $(D_1,\xi)$) such that for every realization of $D_1$, $t(\xi)$ with $\xi\sim P$ is a continuous (atomless) random variable. Let
--   $$U(D)=\{\xi:\ t(\xi)\le s\},\qquad s=t(\xi^2_{(i^*)}),$$
--   the $i^*$-th smallest of $t(\xi^2_1),\dots,t(\xi^2_{n_2})$, with $i^*=\min\{r:\sum_{k=0}^{r-1}\binom{n_2}{k}(1-\epsilon)^k\epsilon^{n_2-k}\ge 1-\delta,\ 1\le r\le n_2\}$ as in (4). Then:
--
--   1. the event $\{P(\xi\in U(D))\ge 1-\epsilon\}$ is measurable and $U$ satisfies (3):
--   $$P_D\big(P(\xi\in U(D))\ge 1-\epsilon\big)\ge 1-\delta ;$$
--   2. on that event, every decision $x$ feasible for the robust program (2) with $U(D)$ ($g(x;\xi)\in A$ for all $\xi\in U(D)$) is feasible for the chance-constrained program (1): $P(g(x;\xi)\in A)\ge 1-\epsilon$;
--   3. consequently, with $P_D$-probability at least $1-\delta$, every feasible (in particular every optimal) solution of (2) using $U(D)$ is feasible for (1).
--
--   The required Phase 2 sample size depends only on $\epsilon$ and $\delta$, not on the dimension of the decision or of the data; for $\epsilon=\delta=0.05$ it is $59$.
--
--   Differences from the source:
--   - reading: ϵ, δ tolerance and confidence levels (range not stated) → 0 < ϵ < 1, 0 < δ < 1; reason: the meaningful range; log(1 − ϵ) requires ϵ < 1
--   - reading: t(ξ) is a continuous random variable → the law of t(d₁, ξ), ξ ~ P, is atomless for every realization d₁ of D₁; reason: the weakest standard meaning of continuous
--   - encoding: P a continuous distribution → not assumed separately; reason: atomlessness of P follows from that of t(ξ) (an atom a of P gives the atom t(a) of t(ξ))
--   - reading: t : ℝᵐ → ℝ a map constructed from D₁ → a jointly measurable function t(D₁, ξ) of D₁ and ξ; reason: the probabilities over D of events built from t presume measurability; t never depends on D₂
--   - encoding: an i.i.d. data set D partitioned into D₁ and D₂ → the product law P^{n₁} ⊗ P^{n₂} on (Fin n₁ → E) × (Fin n₂ → E); reason: the partition is fixed in advance
--   - encoding: ranked observations t(ξ²₍₁₎) < ⋯ < t(ξ²₍ₙ₂₎) → order statistics with multiplicity via Tuple.sort, 1-based rank i*, 0-based Fin indices; reason: ties have probability 0 under the hypotheses
--   - encoding: U satisfies (3) → the event is measurable (a conclusion) and has probability ≥ 1 − δ; reason: so the probability is a genuine measure, not an outer-measure value
--   - generalization: an optimal solution obtained from (2) using this U is feasible for (1) with confidence 1 − δ → on the event of (3) every RO-feasible x is CCP-feasible, and the event that every RO-feasible x is CCP-feasible has probability ≥ 1 − δ; decisions X and outcomes Ω arbitrary types; reason: every optimal solution is feasible and the event does not depend on the solution chosen, so it specializes to the paper's claim
--   - generalization: ξ ∈ ℝᵐ → any measurable space E; reason: the paper's case is E = ℝᵐ
--   - encoding: log → Real.log, n₂ cast to ℝ; reason: Lean convention
-- source:
--   Hong–Huang–Lam, arXiv:1704.04342v2, Theorem 1, p.9 (proof p.9)

import Mathlib
import Definitions.Def_LearningBasedRO_Model

open MeasureTheory

namespace LearningBasedRO

/-- **Theorem 1 (Basic statistical guarantee).** Let the i.i.d. data from a continuous
distribution `P` be split into `D₁` (`n₁` points) and `D₂` (`n₂` points) with
`n₂ ≥ log δ / log(1 - ϵ)`. Let `t` be a score map constructed from `D₁` such that `t(ξ)`,
`ξ ~ P`, is a continuous random variable, and `U(D) = {ξ : t(ξ) ≤ t(ξ²₍ᵢ*₎)}` with `i*` of (4).
Then `U` satisfies (3), and consequently, with confidence `1 - δ`, every feasible solution of
(2) using `U(D)` (in particular an optimal one) is feasible for (1).
Hong–Huang–Lam, arXiv:1704.04342v2, Theorem 1, p.9 (proof p.9).

**Formalization Note** Conclusions: the event `E₃ = {D : P(U(D)) ≥ 1 - ϵ}` is measurable, it has
probability `≥ 1 - δ` under the split-sample law `P^{n₁} ⊗ P^{n₂}` (this is (3)), on `E₃` every
RO-feasible decision is CCP-feasible, and hence the set of data on which every RO-feasible
decision is CCP-feasible has probability `≥ 1 - δ`. The data space `E` is any measurable space
(the page: `ℝᵐ`); decisions `X` and outcomes `Ω` are arbitrary types. "Continuous" is read as
atomless; `P` itself is then atomless automatically. `t` is a jointly measurable function of
`(D₁, ξ)`. `0 < ϵ < 1`, `0 < δ < 1`; `log` is `Real.log`. -/
theorem theorem_1 {E X Ω : Type*} [MeasurableSpace E] (P : Measure E) [IsProbabilityMeasure P]
    (n₁ n₂ : ℕ) (ϵ δ : ℝ) (hϵ0 : 0 < ϵ) (hϵ1 : ϵ < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hn₂ : Real.log δ / Real.log (1 - ϵ) ≤ (n₂ : ℝ)) (t : (Fin n₁ → E) → E → ℝ)
    (ht : Measurable (Function.uncurry t)) (hcont : ∀ d₁, NullSingletonClass (P.map (t d₁)))
    (g : X → E → Ω) (A : Set Ω) :
    MeasurableSet {D : (Fin n₁ → E) × (Fin n₂ → E) | IsContentSet P ϵ (uncertaintySet t ϵ δ D)} ∧
      SatisfiesReq3 (splitLaw P n₁ n₂) P ϵ δ (uncertaintySet t ϵ δ) ∧
      (∀ D : (Fin n₁ → E) × (Fin n₂ → E), IsContentSet P ϵ (uncertaintySet t ϵ δ D) →
        ∀ x : X, ROFeasible g A (uncertaintySet t ϵ δ D) x → CCPFeasible P g A ϵ x) ∧
      ENNReal.ofReal (1 - δ) ≤
        splitLaw P n₁ n₂ {D | ∀ x : X, ROFeasible g A (uncertaintySet t ϵ δ D) x →
          CCPFeasible P g A ϵ x} := by sorry

end LearningBasedRO
