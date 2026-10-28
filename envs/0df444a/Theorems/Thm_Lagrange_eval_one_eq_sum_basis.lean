-- Prove2me | Theorems.Thm_Lagrange_eval_one_eq_sum_basis
-- name    : Lagrange.eval_one_eq_sum_basis
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-27T00:30:13.197878+00:00
-- url     : https://prove2.me/theorems/03f774db-0417-4567-94a6-9170f3e082e1
-- title:
--   Lagrange interpolation evaluates a low-degree polynomial at any point
-- statement:
--   Let $v_0, \dots, v_d$ be $d+1$ distinct real numbers (the interpolation nodes) and let
--   $\ell_i$ denote the Lagrange basis polynomial attached to the node $v_i$, so that
--   $\ell_i(v_j) = \delta_{ij}$. If $p$ is a real polynomial with $\deg p \le d$, then its value at
--   $1$ is determined by its values at the nodes:
--
--   $$
--   p(1) \;=\; \sum_{i=0}^{d} \ell_i(1)\, p(v_i).
--   $$
--
--   A polynomial of degree at most $d$ has $d+1$ degrees of freedom, so its value anywhere is a
--   fixed linear combination of its values at any $d+1$ distinct points, with coefficients that
--   depend on the nodes alone and not on $p$. The useful direction in applications is the converse
--   reading: to control $p(1)$ it suffices to control $p$ on a set of nodes one is free to choose,
--   for instance inside a small interval.
--
--   **Formalization Note** $\ell_i$ is `Lagrange.basis Finset.univ v i` and the hypothesis on the
--   nodes is injectivity of `v : Fin (d+1) → ℝ`.
-- source:
--   Lagrange interpolation; see e.g. P. J. Davis, Interpolation and Approximation, Dover 1975, §2.5. Carved from the accepted proof of ChanPangGQVI.ProjExistence.theorem_5_2, https://prove2.me/submissions/08ed2756-557a-470f-8493-8c93e6b779c8

import Mathlib

open Metric Set MeasureTheory
open Polynomial

theorem Lagrange.eval_one_eq_sum_basis {d : ℕ} (v : Fin (d+1) → ℝ) (hv : Function.Injective v) (p : ℝ[X])
    (hp : p.natDegree ≤ d) :
    p.eval 1 = ∑ i, (Lagrange.basis Finset.univ v i).eval 1 * p.eval (v i) := by sorry
