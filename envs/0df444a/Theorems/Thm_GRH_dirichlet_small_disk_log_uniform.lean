-- Prove2me | Theorems.Thm_GRH_dirichlet_small_disk_log_uniform
-- name    : GRH.dirichlet_small_disk_log_uniform
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T00:28:41.884177+00:00
-- url     : https://prove2.me/theorems/8d3b5652-26b7-4c3d-bbfb-ff27b997baa3
-- title:
--   Uniformly bounded holomorphic logarithms of Dirichlet L-functions on disks centered on real part two
-- statement:
--   There is an absolute $A\ge1$ with the following property. For every Dirichlet character $\chi$ of positive modulus and every $c$ with $\operatorname{Re}c=2$, the function $L(\cdot,\chi)$ admits a holomorphic logarithm on $|s-c|<1/2$ whose modulus is at most $A$ on $|s-c|\le49/100$. The same $A$ works for principal and nonprincipal characters and at every height.
-- source:
--   Uniform Dirichlet-character generalization of the small-disk step of https://prove2.me/theorems/242af0ad-5520-48fe-b514-c52cefbcd1c2 using the normalized analytic logarithm https://prove2.me/theorems/86b4371b-226d-416f-917b-0e1eb876d399, Borel–Carathéodory https://prove2.me/theorems/d92d4067-bfea-42c0-85cd-0ba462067260, and the right-half-plane anchor https://prove2.me/theorems/6164233f-eecb-4cc6-ba54-669f100a3086.

import Mathlib.NumberTheory.LSeries.DirichletContinuation

open Complex Set Metric

theorem GRH.dirichlet_small_disk_log_uniform :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (c : ℂ), c.re = 2 →
      ∃ E : ℂ → ℂ, DifferentiableOn ℂ E (ball c (1 / 2)) ∧
        EqOn (Complex.exp ∘ E) χ.LFunction (ball c (1 / 2)) ∧
        ∀ z ∈ closedBall c (49 / 100), ‖E z‖ ≤ A := by sorry
