-- Prove2me | Theorems.Thm_MarkovMixing_vecMul_pow
-- name    : MarkovMixing.vecMul_pow
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-27T01:08:06.921402+00:00
-- url     : https://prove2.me/theorems/e03fbba8-0da3-4508-b168-fd3d64b11e1e
-- title:
--   A stationary distribution is stationary for every power of the chain
-- statement:
--   Let $P$ be a transition matrix on a finite state space $V$ and let $\pi$ be stationary
--   for $P$, that is $\pi P = \pi$ where $\pi$ acts as a row vector. Then $\pi$ is stationary for
--   every power of $P$:
--
--   $$
--   \pi\, P^{t} \;=\; \pi \qquad \text{for all } t \in \mathbb{N}.
--   $$
--
--   Stationarity is preserved under iteration, so the chain observed every $t$ steps has the same
--   stationary distribution as the chain itself. This is what allows a mixing estimate to be run on
--   $P^t$ rather than $P$ — the standard device for turning a one-step contraction into a
--   geometric rate.
-- source:
--   D. A. Levin, Y. Peres and E. L. Wilmer, Markov Chains and Mixing Times, 2nd ed., AMS 2017, §1.5; carved from the accepted proof of DiaconisStroock.Poincare.proposition_1, https://prove2.me/submissions/b36a2a77-0ed1-410e-b982-dafb4dc643a6

import Mathlib
import Definitions.Def_mm_spectral

open scoped BigOperators
open scoped Matrix
open MarkovMixing
set_option maxHeartbeats 1000000
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem MarkovMixing.vecMul_pow {P : Matrix V V ℝ} {π : V → ℝ} (hπ : IsStationary P π) :
    ∀ t : ℕ, Matrix.vecMul π (P ^ t) = π := by sorry
