-- Prove2me | Theorems.Thm_GRH_dirichlet_zero_free_of_prime_lower_bound_in_identity_class
-- name    : GRH.dirichlet_zero_free_of_prime_lower_bound_in_identity_class
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-27T01:44:59.771283+00:00
-- url     : https://prove2.me/theorems/a9626e58-bba6-5e1e-8672-5c25fc1dbd17
-- title:
--   One lower estimate on ordinary primes in class 1 excludes every character zero at a fixed modulus
-- statement:
--   Fix q>0 and 1/2≤θ<1. If at every square u² the log-weight of ordinary primes congruent to 1 modulo q satisfies φ(q)∑log p ≥ u²−C(u²+1)^θ for some C≥0, then every Dirichlet L-function modulo q is nonzero in Re(s)>θ away from the principal pole.
-- source:
--   Arithmetic reduction for GRH.centered_moebius_progression_bilinear_power_bound. The fixed-modulus equivalence is https://prove2.me/theorems/04e865ba-3dd7-43e6-9714-8e4d666e0b7c .

import Definitions.Def_GRH_SplitPrimeLower

open GRH.SplitPrimeLower

theorem GRH.dirichlet_zero_free_of_prime_lower_bound_in_identity_class (q : ℕ) [NeZero q] (θ : ℝ) (hθ : (1/2:ℝ) ≤ θ) (hθ1 : θ<1)
    (h : squareLower q θ) :
    ∀ (χ : DirichletCharacter ℂ q) (s : ℂ), θ<s.re → ¬ (χ=1 ∧ s=1) → χ.LFunction s ≠ 0 := by sorry
