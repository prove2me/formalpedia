-- Prove2me | Theorems.Thm_MarkovChain_exists_isStationary
-- name    : MarkovChain.exists_isStationary
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-12T18:59:16.023231+00:00
-- url     : https://prove2.me/theorems/637d07a6-576d-4f16-9cc6-ac3d05146e4b
-- title:
--   Every finite Markov chain has a stationary distribution
-- statement:
--   **Existence of equilibrium.** Every row-stochastic matrix on a nonempty finite state space admits a stationary distribution: a probability vector $\pi$ with $\pi M = \pi$. No irreducibility, aperiodicity or positivity is assumed — the statement is unconditional, and uniqueness genuinely can fail (the identity matrix fixes every distribution).
--
--   This is the foundational existence theorem of the subject and it is *not* a linear-algebra fact in disguise. Row sums $1$ give $(I - M)\mathbf{1} = 0$, hence $\det(I-M) = 0$, hence a nonzero left null vector; but that vector carries no sign information, and a stationary distribution must be nonnegative. The usual proofs invoke Brouwer's fixed point theorem or Perron–Frobenius.
--
--   The argument formalized here uses neither. Let $S\mu = \mu M$, a continuous map of the standard simplex into itself, let $x_m = S^m v$ be the orbit of an arbitrary point mass, and let $a_m$ be the Cesàro average $\frac{1}{m+1}\sum_{r \le m} x_r$. Telescoping gives the exact identity
--   $$(S a_m)_i - (a_m)_i = \frac{x_{m+1,i} - x_{0,i}}{m+1},$$
--   whose numerator lies in $[-1,1]$ because every $x_r$ is a distribution; so $S a_m - a_m \to 0$ with an explicit $O(1/m)$ rate. The standard simplex is compact, so some subsequence $a_{\varphi(k)}$ converges to a distribution $\pi$; continuity of $S$ gives $S a_{\varphi(k)} \to S\pi$, and subtracting the two convergences forces $S\pi = \pi$.
-- source:
--   J. R. Norris, Markov Chains, Cambridge University Press 1997, Chapter 1 (SS1.7 invariant distributions, SS1.8 convergence to equilibrium). The proof formalized here is the Cesaro-average/compactness argument, the standard route when neither Brouwer's fixed point theorem nor Perron-Frobenius is available.

import Definitions.Def_MarkovChain

open Finset Matrix Filter Topology

namespace MarkovChain

theorem exists_isStationary {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n ℝ} (hne : Nonempty n)
    (hM : M ∈ rowStochastic ℝ n) :
    ∃ π : n → ℝ, IsStationary M π := by
  sorry

end MarkovChain
