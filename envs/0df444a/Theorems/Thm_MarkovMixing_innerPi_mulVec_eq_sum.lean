-- Prove2me | Theorems.Thm_MarkovMixing_innerPi_mulVec_eq_sum
-- name    : MarkovMixing.innerPi_mulVec_eq_sum
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-27T01:08:04.118992+00:00
-- url     : https://prove2.me/theorems/1dcb6b61-6307-474b-a8ba-15d7b3b380ac
-- title:
--   The quadratic form of the chain in its eigenbasis
-- statement:
--   Under the same hypotheses, the $\ell^2(\pi)$ quadratic form of the transition matrix
--   diagonalizes:
--
--   $$
--   \langle g,\, P g \rangle_{\pi} \;=\; \sum_{j} \lambda_j\, \langle g, f_j \rangle_{\pi}^{2}.
--   $$
--
--   Together with the Parseval identity and the expression of the Dirichlet form as
--   $\langle g,g\rangle_\pi - \langle g, Pg\rangle_\pi$, this turns the variational problem for the
--   spectral gap into a problem about a weighted sum of squares, where the extremum is attained by
--   putting all the mass on one eigenvalue. That is the step that identifies the gap with
--   $1 - \lambda_2$.
-- source:
--   D. A. Levin, Y. Peres and E. L. Wilmer, Markov Chains and Mixing Times, 2nd ed., AMS 2017, Lemma 12.2 and §13.3; carved from the accepted proof of DiaconisStroock.Poincare.proposition_1, https://prove2.me/submissions/b36a2a77-0ed1-410e-b982-dafb4dc643a6

import Mathlib
import Definitions.Def_mm_spectral

open scoped BigOperators
open scoped Matrix
open MarkovMixing
set_option maxHeartbeats 1000000
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {P : Matrix V V ℝ} {π : V → ℝ} {n : ℕ} {lam : Fin n → ℝ} {ff : Fin n → V → ℝ}

theorem MarkovMixing.innerPi_mulVec_eq_sum (heig : ∀ j, P.mulVec (ff j) = lam j • ff j) (hpos : ∀ x, 0 < π x)
    (hcomp : ∀ x y : V, ∑ j, ff j x * ff j y = (if x = y then 1 else 0) / π y)
    (g : V → ℝ) :
    innerPi π g (P.mulVec g) = ∑ j, lam j * (innerPi π g (ff j)) ^ 2 := by sorry
