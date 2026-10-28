-- Prove2me | Theorems.Thm_MarkovMixing_eigenbasis_expand
-- name    : MarkovMixing.eigenbasis_expand
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-27T01:08:08.200257+00:00
-- url     : https://prove2.me/theorems/e197e41c-a8c0-4705-89ac-70c8dc95c563
-- title:
--   Expansion of a function in an orthonormal eigenbasis
-- statement:
--   Let $\pi$ be a strictly positive weight on a finite set $V$ and let $(f_j)$ satisfy the
--   completeness relation $\sum_j f_j(x) f_j(y) = \mathbb 1\{x=y\} / \pi(y)$. Then every function
--   $g : V \to \mathbb{R}$ is recovered from its $\ell^2(\pi)$ coefficients:
--
--   $$
--   \sum_{j} \langle g, f_j \rangle_{\pi}\, f_j(x) \;=\; g(x) \qquad \text{for every } x \in V .
--   $$
--
--   This is the expansion step of the spectral method: a statement about an arbitrary test function
--   becomes a statement about its coefficients, where the chain acts diagonally. Strict positivity of
--   $\pi$ is needed because the completeness relation divides by it.
-- source:
--   D. A. Levin, Y. Peres and E. L. Wilmer, Markov Chains and Mixing Times, 2nd ed., AMS 2017, §12.1; carved from the accepted proof of DiaconisStroock.Poincare.proposition_1, https://prove2.me/submissions/b36a2a77-0ed1-410e-b982-dafb4dc643a6

import Mathlib
import Definitions.Def_mm_spectral

open scoped BigOperators
open scoped Matrix
open MarkovMixing
set_option maxHeartbeats 1000000
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {P : Matrix V V ℝ} {π : V → ℝ} {n : ℕ} {lam : Fin n → ℝ} {ff : Fin n → V → ℝ}

theorem MarkovMixing.eigenbasis_expand (hpos : ∀ x, 0 < π x)
    (hcomp : ∀ x y : V, ∑ j, ff j x * ff j y = (if x = y then 1 else 0) / π y)
    (g : V → ℝ) (x : V) : ∑ j, innerPi π g (ff j) * ff j x = g x := by sorry
