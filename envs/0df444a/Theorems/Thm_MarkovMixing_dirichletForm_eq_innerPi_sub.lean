-- Prove2me | Theorems.Thm_MarkovMixing_dirichletForm_eq_innerPi_sub
-- name    : MarkovMixing.dirichletForm_eq_innerPi_sub
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-27T01:08:02.616673+00:00
-- url     : https://prove2.me/theorems/6142c9e6-e803-4ade-8a25-ea081483c65b
-- title:
--   The Dirichlet form as an $ℓ^2(π)$ quadratic form
-- statement:
--   Let $P$ be a stochastic matrix on a finite state space $V$ with stationary distribution
--   $\pi$, and for $g : V \to \mathbb{R}$ let
--
--   $$
--   \mathcal E(g) \;=\; \tfrac12 \sum_{x,y} \pi(x)\, P(x,y)\,\bigl(g(x) - g(y)\bigr)^{2}
--   $$
--
--   be the Dirichlet form of the chain. Then $\mathcal E$ is the quadratic form of $I - P$ in
--   $\ell^2(\pi)$:
--
--   $$
--   \mathcal E(g) \;=\; \langle g, g \rangle_{\pi} \;-\; \langle g,\, P g \rangle_{\pi}.
--   $$
--
--   This identity is the hinge of the variational theory of the spectral gap. The left-hand side is a
--   sum over edges, which is what a combinatorial or geometric argument can bound (by a congestion,
--   a bottleneck or a canonical-path estimate); the right-hand side is a spectral quantity, which is
--   what controls the mixing time. Every Poincaré-inequality argument crosses from one to the
--   other here.
-- source:
--   D. A. Levin, Y. Peres and E. L. Wilmer, Markov Chains and Mixing Times, 2nd ed., AMS 2017, Lemma 13.11 and §13.3; carved from the accepted proof of DiaconisStroock.Poincare.proposition_1, https://prove2.me/submissions/b36a2a77-0ed1-410e-b982-dafb4dc643a6

import Mathlib
import Definitions.Def_mm_spectral

open scoped BigOperators
open scoped Matrix
open MarkovMixing
set_option maxHeartbeats 1000000
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem MarkovMixing.dirichletForm_eq_innerPi_sub {P : Matrix V V ℝ} {π : V → ℝ} (hP : IsStochastic P)
    (hπ : IsStationary P π) (g : V → ℝ) :
    dirichletForm P π g = innerPi π g g - innerPi π g (P.mulVec g) := by sorry
