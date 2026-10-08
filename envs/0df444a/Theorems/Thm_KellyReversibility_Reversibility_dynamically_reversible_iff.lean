-- Prove2me | Theorems.Thm_KellyReversibility_Reversibility_dynamically_reversible_iff
-- name    : KellyReversibility.Reversibility.dynamically_reversible_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T02:36:19.174447+00:00
-- url     : https://prove2.me/theorems/c88cffe9-aeb1-4456-81fb-b6c6aa5effba
-- title:
--   Theorem 1.14 — dynamic reversibility iff $\pi(j)=\pi(j^+)$ and $\pi(j)q(j,k)=\pi(k^+)q(k^+,j^+)$
-- statement:
--   Let $X(t)$ be a stationary Markov process on a finite state space $\mathcal S$ with transition rates $q(j,k)$ ($q(j,j)=0$), irreducible, with equilibrium distribution $\pi_0$. Let $j\mapsto j^+$ be a conjugation of the states, $(j^+)^+=j$, and suppose $q(j)=q(j^+)$ for $j\in\mathcal S$, where $q(j)=\sum_k q(j,k)$. Then:
--
--   1. $X$ is dynamically reversible (statistically indistinguishable from $[X(\tau-t)]^+$) if and only if there exists a collection of positive numbers $\pi(j)$, $j\in\mathcal S$, summing to unity that satisfy
--   $$\pi(j)=\pi(j^+),\quad j\in\mathcal S, \tag{1.29}$$
--   $$\pi(j)q(j,k)=\pi(k^+)q(k^+,j^+),\quad j,k\in\mathcal S;$$
--   2. when such a collection exists, it is the equilibrium distribution: $\pi=\pi_0$.
--
--   With the identity conjugation this is Theorem 1.3.
--
--   **Formalization Note** Dynamic reversibility is the distributional statement $P(X(t_r)=j_r\ \forall r)=P(X(\tau-t_r)=j_r^+\ \forall r)$ for all time points, states and $\tau$. The state space is finite.
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, p. 31, Theorem 1.14, Eq. (1.29) (dynamic reversibility defined on p. 31)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance
import Definitions.Def_KellyReversibility_Reversibility_StationaryLaw
import Definitions.Def_KellyReversibility_Reversibility_MarkovProcess

namespace KellyReversibility.Reversibility

/-- Theorem 1.14 (Kelly, p. 31). -/
theorem dynamically_reversible_iff {S : Type*} [Fintype S] [DecidableEq S]
    (q : S → S → ℝ) (hq : ∀ j k, j ≠ k → 0 ≤ q j k) (hq0 : ∀ j, q j j = 0)
    (hirr : RatesIrreducible q)
    (conj : S → S) (hconj : Function.Involutive conj)
    (hqc : ∀ j, ∑ k, q j k = ∑ k, q (conj j) k)
    (π₀ : S → ℝ) (hπ₀ : IsEquilibrium π₀ q) :
    (DynamicallyReversible q π₀ conj ↔
      ∃ π : S → ℝ, (∀ j, 0 < π j) ∧ ∑ j, π j = 1 ∧ (∀ j, π j = π (conj j)) ∧
        ∀ j k, π j * q j k = π (conj k) * q (conj k) (conj j)) ∧
    ∀ π : S → ℝ, (∀ j, 0 < π j) → ∑ j, π j = 1 → (∀ j, π j = π (conj j)) →
      (∀ j k, π j * q j k = π (conj k) * q (conj k) (conj j)) → π = π₀ := by sorry

end KellyReversibility.Reversibility
