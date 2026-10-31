-- Prove2me | Theorems.Thm_GenSwitchHT_lemma_4
-- name    : GenSwitchHT.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:20:38.755405+00:00
-- url     : https://prove2.me/theorems/0cc8701c-b027-4376-b7d8-5fb5c6134483
-- title:
--   Lemma 4 — negative drift and bounded increments give a bounded exponential moment
-- statement:
--   Let $\eta>0$, $\tau$ and $D$ be real numbers. There are $\theta^\star>0$ and $C^\star<\infty$, depending only on $\eta,\tau,D$, with the following property. Let $(X(k))$ be a Markov chain with one-step kernel $\mathrm{step}$, and let $Z\ge0$ be a function on its state space such that
--
--   1. (C1) $\mathbb E[Z(X(k+1))-Z(X(k))\mid X(k)=x]\le-\eta$ whenever $Z(x)\ge\tau$;
--   2. (C2) $|Z(X(k+1))-Z(X(k))|\le D$ with probability one from every state.
--
--   Then
--
--   $$
--   \limsup_{k\to\infty}\mathbb E\bigl[e^{\theta^\star Z(X(k))}\mid X(0)=x\bigr]\le C^\star\quad\text{for every state }x,
--   $$
--
--   and $\mathbb E[e^{\theta^\star Z(\bar X)}]\le C^\star$ whenever $\bar X$ has a stationary law of the chain. Further, if the state space is countable and the chain is irreducible, aperiodic and positive recurrent, then the laws of $X(k)$ converge pointwise, from every initial state, to a law $\varpi$ with $\mathbb E_\varpi[e^{\theta^\star Z}]\le C^\star$.
--
--   In Lean, irreducible means that every state reaches every state; aperiodic is written as $P^k(x,x)>0$ for all large $k$, at every state; positive recurrent is written as the existence of a stationary law. For an irreducible chain on a countable state space these are equivalent to the usual definitions.
--
--   This is the form of Hajek's drift theorem that yields all moments of a steady state. The dependence of the constants on $\eta,\tau,D$ alone is what makes moment bounds uniform along a family of chains.
--
--   **Formalization Note** The expectations are in $[0,\infty]$, so their finiteness is part of the bound.
--
--   Differences from the source:
--   - generalization: θ⋆, C⋆ chosen for one irreducible aperiodic chain on a countable state space → θ, C chosen from η, τ, D before the chain; the first two clauses for any PMF kernel on any type; reason: this implies the printed form, and Appendix B needs it: it applies the lemma to a family of chains
--   - generalization: if the chain is positive recurrent, it converges in distribution to Z̄ with E[e^{θ⋆Z̄}] ≤ C⋆ → this clause (pointwise convergence of the k-step laws from every state to a PMF ϖ with the bound), and in addition the bound for every stationary PMF of any chain satisfying (C1)–(C2), with no irreducibility, aperiodicity or countability; reason: the added clause is extra content; the printed clause is stated as printed
--   - encoding: irreducible, aperiodic, positive recurrent → every state reaches every state; step^k(x)(x) ≠ 0 for all large k at every x; a stationary PMF exists; reason: for an irreducible chain on a countable state space each is equivalent to the usual definition
--   - encoding: limsup and expectations of a real random variable → ℝ≥0∞-valued series and limsup; reason: a real limsup has a junk value on unbounded sequences
-- source:
--   Hurtado-Lange–Maguluri, Heavy-traffic Analysis of Queueing Systems with no Complete Resource Pooling, arXiv:1904.10096v4, Lemma 4, p.34

import Mathlib
import Definitions.Def_GenSwitchHT_Model

open scoped BigOperators Matrix Topology ENNReal

universe u

namespace GenSwitchHT

/-- Lemma 4 of Hurtado-Lange–Maguluri, Heavy-traffic Analysis of Queueing Systems with no Complete Resource Pooling, arXiv:1904.10096v4, p.34
(a corollary of Hajek's drift theorem): if `Z ≥ 0` has drift at most `-η` when `Z ≥ τ` (C1) and
one-step increments bounded by `D` (C2), then the chain has a bounded exponential moment.

**Formalization Note.**
1. `θ` and `C` are chosen before the chain: they depend on `η, τ, D` only. The paper's Appendix B
applies the lemma to a family of chains indexed by `ε`, and needs this.
2. Irreducibility, aperiodicity and countability of `X` are assumed only in the last clause.
3. The moments are in `ℝ≥0∞`, so no summability has to be stated and `limsup` has no junk value.
4. The first clause starts from a point, and is the printed `limsup` bound.
5. The second clause gives the bound for every stationary law, with no further assumption.
6. The last clause is the printed second clause: for an irreducible aperiodic positive recurrent
chain on a countable state space, the chain converges in distribution (pointwise convergence of
the `k`-step laws, from every starting point) to a law `ϖ` with `E_ϖ[e^{θZ}] ≤ C`. Irreducible:
every state reaches every state. Aperiodic: written as "`step^k(x)(x) > 0` for all large `k`",
which is equivalent to period `1` for an irreducible chain. Positive recurrent: written as "a
stationary `PMF` exists", which is equivalent for an irreducible chain on a countable space. -/
theorem lemma_4 (η τ D : ℝ) (hη : 0 < η) :
    ∃ θ C : ℝ, 0 < θ ∧ 0 < C ∧
      ∀ (X : Type u) (step : X → PMF X) (Z : X → ℝ), (∀ x, 0 ≤ Z x) →
        (∀ x, τ ≤ Z x → expect (step x) (fun y => Z y - Z x) ≤ -η) →
        (∀ x, ∀ y ∈ (step x).support, |Z y - Z x| ≤ D) →
        (∀ x, Filter.limsup
            (fun k => ∑' y, iterateKernel step k x y * ENNReal.ofReal (Real.exp (θ * Z y)))
            Filter.atTop ≤ ENNReal.ofReal C) ∧
        (∀ ϖ : PMF X, ϖ.bind step = ϖ →
          ∑' x, ϖ x * ENNReal.ofReal (Real.exp (θ * Z x)) ≤ ENNReal.ofReal C) ∧
        (Countable X →
          (∀ x y, ∃ k, iterateKernel step k x y ≠ 0) →
          (∀ x, ∃ K : ℕ, ∀ k, K ≤ k → iterateKernel step k x x ≠ 0) →
          (∃ ϖ : PMF X, ϖ.bind step = ϖ) →
          ∃ ϖ : PMF X,
            (∀ x₀ y, Filter.Tendsto (fun k => iterateKernel step k x₀ y) Filter.atTop (𝓝 (ϖ y))) ∧
            ∑' x, ϖ x * ENNReal.ofReal (Real.exp (θ * Z x)) ≤ ENNReal.ofReal C) := by sorry

end GenSwitchHT
