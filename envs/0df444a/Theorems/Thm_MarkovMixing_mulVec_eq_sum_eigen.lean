-- Prove2me | Theorems.Thm_MarkovMixing_mulVec_eq_sum_eigen
-- name    : MarkovMixing.mulVec_eq_sum_eigen
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-27T01:08:10.825243+00:00
-- url     : https://prove2.me/theorems/294d45ab-6cd9-4b7f-9b26-7d4c16b5d0b0
-- title:
--   The chain acts diagonally in its eigenbasis
-- statement:
--   Let $\pi$ be a strictly positive weight on a finite set $V$, let $(f_j)$ satisfy the
--   completeness relation, and let each $f_j$ be an eigenfunction of the transition matrix $P$ with
--   eigenvalue $\lambda_j$, so $P f_j = \lambda_j f_j$. Then for every $g : V \to \mathbb{R}$ and
--   every $x \in V$,
--
--   $$
--   (P g)(x) \;=\; \sum_{j} \langle g, f_j \rangle_{\pi}\, \lambda_j\, f_j(x).
--   $$
--
--   Applying the chain multiplies the $j$-th coefficient by $\lambda_j$. This is the whole point of
--   the eigenbasis, and the identity from which the decay of $P^t$ — and hence every spectral
--   bound on the mixing time — is read off.
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

theorem MarkovMixing.mulVec_eq_sum_eigen (heig : ∀ j, P.mulVec (ff j) = lam j • ff j) (hpos : ∀ x, 0 < π x)
    (hcomp : ∀ x y : V, ∑ j, ff j x * ff j y = (if x = y then 1 else 0) / π y)
    (g : V → ℝ) (x : V) :
    (P.mulVec g) x = ∑ j, innerPi π g (ff j) * lam j * ff j x := by sorry
