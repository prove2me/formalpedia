-- Prove2me | Theorems.Thm_LargeCongestion_Poisson_Supplement_theorem_4
-- name    : LargeCongestion.Poisson.Supplement.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T07:34:41.497769+00:00
-- url     : https://prove2.me/theorems/fa4d1e10-d02f-4029-a761-21ca4924385a
-- title:
--   Theorem 4 — arbitrary bounded-cost Bernoulli games converge to Poisson-game equilibria
-- statement:
--   Let $T$ be a finite set of types with arbitrary nonempty finite action spaces $A_t$. The fixed real cost $C(n;t,a)$ may depend on the whole vector of other active players' strategy counts, as well as the player's type and chosen action. Assume it is bounded over all count vectors for each type and action.
--
--   Consider finite games with independently participating players of types $\tau_i^n$, participation probabilities $u_i^n\in(0,1]$, and independent, possibly asymmetric mixed strategies $\hat\sigma_i^n$ forming a Nash equilibrium. Assume (14): the player counts diverge, maximum participation tends to zero, and per-type expected demands tend to $d_t>0$. The induced expected counts are
--   $$y^n_{t,a}=\mathbb E[Y^n_{t,a}]=\sum_{i:\tau_i^n=t}u_i^n\hat\sigma_i^n(a).$$
--   Their vector sequence is bounded. Every accumulation vector $\hat y$ defines an equilibrium of the Poisson game with populations of means $d_t$ and the same cost $C$, by
--   $$\hat q_t(a)=\frac{\hat y_{t,a}}{d_t}.$$
--   The conclusion includes that these are probability vectors and that the posterior expected costs are well defined. This companion result covers general count-vector interactions beyond separable congestion costs.
--
--   Differences from the source:
--   - encoding: arbitrary finite strategy sets and finite individual players → dependent finite action types A_t and players Fin N, with all counts indexed by the type-action sum type; reason: no resource-subset representation or type symmetry is imposed on the finite games
--   - encoding: every accumulation point and convergent subsequence → limits along every strictly increasing map from natural numbers; reason: the vectors are finite dimensional, so this is exactly the sequential accumulation-point criterion
--   - encoding: C is bounded for each type and action → one bound controls the absolute cost uniformly over counts and type-action pairs; reason: there are finitely many type-action pairs, so this is equivalent to the printed boundedness assumption
--   - encoding: ordinary Poisson posterior expected costs → summability is included in the resulting equilibrium predicate; reason: bounded costs and probability laws give these finite expectations; no extra integrability premise is imposed
-- source:
--   Cominetti, Scarsini, Schröder & Stier-Moses, Approximation and Convergence of Large Atomic Congestion Games, arXiv:2001.02797v7, Theorem 4, p. 23

import Mathlib
import Definitions.Def_LargeCongestion_Poisson_Supplement_FinitePopulation
import Definitions.Def_LargeCongestion_Poisson_Supplement_PoissonCongestion

namespace LargeCongestion.Poisson.Supplement
open Filter
open scoped Topology

theorem theorem_4 {T : Type*} [Fintype T] [DecidableEq T]
    (A : T → Type*) [∀ t, Fintype (A t)] [∀ t, DecidableEq (A t)] [∀ t, Nonempty (A t)]
    (C : (Sigma A → ℕ) → Sigma A → ℝ) (hC : BoundedPopulationCosts C)
    (N : ℕ → ℕ) (τ : ∀ n, Fin (N n) → T) (u : ∀ n, Fin (N n) → ℝ)
    (hu : ∀ n, IsBernoulliGame (u n)) (d : T → ℝ) (hd : ∀ t, 0 < d t)
    (h14 : Condition14 N τ u d) (σ : ∀ n i, A (τ n i) → ℝ)
    (heq : ∀ n, (FinitePopulationGame.mk (τ n) (u n) C).IsNash (σ n)) :
    Bornology.IsBounded (Set.range (fun n => bMean (τ n) (u n) (σ n))) ∧
    ∀ (φ : ℕ → ℕ), StrictMono φ → ∀ y : Sigma A → ℝ,
      Tendsto (fun n => bMean (τ (φ n)) (u (φ n)) (σ (φ n))) atTop (𝓝 y) →
      (poissonGame d C).IsEquilibrium (fun t a => y ⟨t, a⟩ / d t) := by sorry

end LargeCongestion.Poisson.Supplement
