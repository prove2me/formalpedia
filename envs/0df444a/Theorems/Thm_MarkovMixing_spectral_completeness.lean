-- Prove2me | Theorems.Thm_MarkovMixing_spectral_completeness
-- name    : MarkovMixing.spectral_completeness
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-27T01:08:12.168332+00:00
-- url     : https://prove2.me/theorems/d8eb71fc-34f5-4009-a1f8-350625b644a3
-- title:
--   Completeness of an orthonormal eigenbasis at time zero
-- statement:
--   Let $P$ be a chain on a finite state space $V$ with stationary distribution $\pi$, and
--   suppose the $t$-step transition probabilities admit the spectral expansion
--
--   $$
--   \frac{(P^{t})(x,y)}{\pi(y)} \;=\; \sum_{j} f_j(x)\, f_j(y)\, \lambda_j^{\,t}
--   \qquad \text{for all } t \in \mathbb{N},\ x, y \in V,
--   $$
--
--   in terms of eigenvalues $\lambda_j$ and eigenfunctions $f_j$. Then taking $t = 0$ gives the
--   completeness relation
--
--   $$
--   \sum_{j} f_j(x)\, f_j(y) \;=\; \frac{\mathbb 1\{x = y\}}{\pi(y)} .
--   $$
--
--   The eigenfunctions, orthonormal in $\ell^2(\pi)$, resolve the identity. This is the form of
--   completeness that later expansions use: it is what lets an arbitrary function be written in the
--   eigenbasis and what makes the Parseval identity for $\langle g, g\rangle_\pi$ available.
-- source:
--   D. A. Levin, Y. Peres and E. L. Wilmer, Markov Chains and Mixing Times, 2nd ed., AMS 2017, Lemma 12.2 and §12.1; carved from the accepted proof of DiaconisStroock.Poincare.proposition_1, https://prove2.me/submissions/b36a2a77-0ed1-410e-b982-dafb4dc643a6

import Mathlib
import Definitions.Def_mm_spectral

open scoped BigOperators
open scoped Matrix
open MarkovMixing
set_option maxHeartbeats 1000000
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {P : Matrix V V ℝ} {π : V → ℝ} {n : ℕ} {lam : Fin n → ℝ} {ff : Fin n → V → ℝ}

theorem MarkovMixing.spectral_completeness
    (hspec : ∀ (t : ℕ) (x y : V), (P ^ t) x y / π y = ∑ j, ff j x * ff j y * lam j ^ t)
    (x y : V) : ∑ j, ff j x * ff j y = (if x = y then 1 else 0) / π y := by sorry
