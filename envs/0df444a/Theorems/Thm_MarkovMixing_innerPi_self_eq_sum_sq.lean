-- Prove2me | Theorems.Thm_MarkovMixing_innerPi_self_eq_sum_sq
-- name    : MarkovMixing.innerPi_self_eq_sum_sq
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-27T01:08:05.416081+00:00
-- url     : https://prove2.me/theorems/cb0ed0e2-d3cf-49a3-a688-b4911ef10ca7
-- title:
--   Parseval identity in $ℓ^2(π)$
-- statement:
--   Under the same hypotheses — a strictly positive weight $\pi$ on a finite set and a
--   family $(f_j)$ satisfying the completeness relation — the squared $\ell^2(\pi)$ norm of any
--   $g : V \to \mathbb{R}$ is the sum of the squares of its coefficients:
--
--   $$
--   \langle g, g \rangle_{\pi} \;=\; \sum_{j} \langle g, f_j \rangle_{\pi}^{2}.
--   $$
--
--   Parseval's identity for the eigenbasis of a reversible chain. It is the normalization that turns
--   the variational characterization of the spectral gap into a genuine optimization over a sphere:
--   the constraint $\langle g, g\rangle_\pi = 1$ becomes a constraint on the coefficient vector.
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

theorem MarkovMixing.innerPi_self_eq_sum_sq (hpos : ∀ x, 0 < π x)
    (hcomp : ∀ x y : V, ∑ j, ff j x * ff j y = (if x = y then 1 else 0) / π y)
    (g : V → ℝ) : innerPi π g g = ∑ j, (innerPi π g (ff j)) ^ 2 := by sorry
