-- Prove2me | Theorems.Thm_KellyStochasticNetworks_FlowStability_stability_iff
-- name    : KellyStochasticNetworks.FlowStability.stability_iff
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-22T03:50:27.587709+00:00
-- url     : https://prove2.me/theorems/6a1a5e0f-5a53-4402-bed4-edb655b81add
-- title:
--   Theorem 8.2 — stability region of weighted alpha-fair allocations
-- statement:
--   Consider finitely many resources and routes, each route using at least one resource, with positive capacities $C_j$, independent Poisson arrival intensities $\nu_r$, independent exponential file-size parameters $\mu_r$, positive weights $w_r$, and $\alpha>0$. At every state $n\in\mathbb N^R$, let $X_r(n)=n_rx_r(n)$ be the weighted $\alpha$-fair aggregate allocation. The countable Markov process has birth rates $\nu_r$ and departure rates $\mu_rX_r(n)$ on active routes. Write $\rho_r=\nu_r/\mu_r$.
--
--   The process is positive recurrent, equivalently it has an equilibrium probability distribution, if and only if
--   $$\sum_{r:j\in r}\rho_r<C_j\qquad\text{for every resource }j.$$
--   The equivalence includes failure of positive recurrence at equality as well as above capacity. It characterizes the full stochastic stability region, beyond the deterministic drift inequality.
--
--   **Formalization Note** Equilibrium means invariance under every nonnegative-time transition kernel of the explicit bounded-rate Poisson uniformization on $\mathbb N^R$. A probability measure on the canonical path space is also required to realize the corresponding stationary Markov finite-dimensional distributions. Counts are not truncated. Existence of an equilibrium distribution, irreducibility, and any drift bound are not assumptions of the theorem. Positive parameter conventions are the standing nondegenerate model used in the source's Lyapunov calculation; an absent route may be omitted.
-- source:
--   Kelly & Yudovina, Stochastic Networks (2014), supplied Lecture Notes PDF, printed p. 189 (PDF p. 197), Theorem 8.2 and (8.2); model on printed pp. 186, 188 (PDF pp. 194, 196)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_FlowStability_Process

namespace KellyStochasticNetworks.FlowStability

/-- Theorem 8.2. Network includes finite 0-1 incidence, a nonempty resource set for
each route, positive capacities, arrival rates, exponential SIZE PARAMETERS mu,
weights, and alpha (all strictly positive). IsAlphaFair maximizes the published aggregate utility at each
count vector, with inactive rates zero and positive active rates. The process has
birth rates nu_r and departure rates mu_r X_r(n), X_r=n_r x_r. PositiveRecurrent
means existence of a probability mass function invariant at EVERY t>=0 under the
Poisson-uniformized transition function on Fin R -> Nat, together with a probability
measure on (NNReal -> (Fin R -> Nat)) whose coordinate process has the stationary
Markov finite-dimensional laws pi(y0) times the product of those transition kernels
for every finite nondecreasing list of nonnegative times. No drift, stationary
law, or process measure is a hypothesis. Subcritical means sum_r A_jr (nu_r/mu_r) < C_j for every j. -/
theorem stability_iff {J R : ℕ} (D : Network J R)
    (X : State R → Fin R → ℝ) (hX : IsAlphaFair D X) :
    PositiveRecurrent D X ↔ Subcritical D := by sorry

end KellyStochasticNetworks.FlowStability
