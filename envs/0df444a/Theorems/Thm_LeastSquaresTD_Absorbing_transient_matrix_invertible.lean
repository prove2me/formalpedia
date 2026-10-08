-- Prove2me | Theorems.Thm_LeastSquaresTD_Absorbing_transient_matrix_invertible
-- name    : LeastSquaresTD.Absorbing.transient_matrix_invertible
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T01:37:47.827761+00:00
-- url     : https://prove2.me/theorems/aade0df5-e8dc-408a-963e-22a0ae5cd6e6
-- title:
--   Proof of Theorem 1 — invertibility of the transient block
-- statement:
--   Let $P$ be the transition matrix of a finite absorbing Markov chain, and let $\mathcal N$ be its non-absorbing states. For every $0\le\gamma\le1$, the principal submatrix of $I-\gamma P$ indexed by $\mathcal N$ is invertible:
--
--   $$
--   C=(I-\gamma P)_{\mathcal N,\mathcal N},\qquad C^{-1}\text{ exists}.
--   $$
--
--   This is the rank claim for the matrix called $C$ in the proof of Theorem 1. The endpoint $\gamma=1$ is included; absorbing reachability is essential there.
-- source:
--   Bradtke and Barto, Linear Least-Squares Algorithms for Temporal Difference Learning, Machine Learning 22 (1996), https://doi.org/10.1023/A:1018056104778, p. 44, Proof of Theorem 1, paragraph defining C

import Definitions.Def_LeastSquaresTD_Absorbing_Chain

namespace LeastSquaresTD.Absorbing

/-- Proof of Theorem 1, p. 44: the non-absorbing block of `I - γP`
has full rank. This includes `γ = 1`, where absorption is essential. -/
theorem transient_matrix_invertible
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (C : Chain X) (γ : ℝ) (habs : C.IsAbsorbing)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    IsUnit ((1 - γ • C.P).submatrix
      (fun x : C.Nonabsorbing => x.val)
      (fun x : C.Nonabsorbing => x.val)) := by sorry

end LeastSquaresTD.Absorbing
