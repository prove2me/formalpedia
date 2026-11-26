-- Prove2me | Theorems.Thm_GRH_nonprincipal_moebius_uniform_power_bound_of_zero_free_halfplane
-- name    : GRH.nonprincipal_moebius_uniform_power_bound_of_zero_free_halfplane
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T13:04:27.500742+00:00
-- url     : https://prove2.me/theorems/da722d6d-0fb6-5db3-99c3-a173783e3f07
-- title:
--   Uniform bounds for Möbius sums twisted by a nonprincipal character from a zero-free half-plane
-- statement:
--   Fix a nonprincipal Dirichlet character $\chi$ modulo a positive integer. Suppose $1/2\le\alpha\le1$ and $L(s,\chi)$ is nonzero for every $\Re(s)>\alpha$. For every real $\sigma>\alpha$ there is $D\ge0$ such that $|\sum_{k\le N}\chi(k)\mu(k)|\le D(N+1)^\sigma$ for every natural cutoff $N$.
-- source:
--   Derived in the centered Möbius bilinear problem https://prove2.me/theorems/5000f709-1ce6-4ce6-a1ad-637c5b963006 and the square-cutoff residue-bias reduction https://prove2.me/theorems/ebfcf6de-c11b-4420-bb99-92e3875c1325.

import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.Complex.Polynomial.Basic

theorem GRH.nonprincipal_moebius_uniform_power_bound_of_zero_free_halfplane (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (α σ : ℝ) (hα : (1/2:ℝ) ≤ α) (h1 : α ≤ 1) (hσ : α < σ)
    (hz : ∀ s : ℂ, α < s.re → χ.LFunction s ≠ 0) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ N : ℕ,
      ‖∑ k ∈ Finset.range (N+1), χ k * (ArithmeticFunction.moebius k : ℂ)‖ ≤
        D * ((N : ℝ)+1)^σ := by sorry
