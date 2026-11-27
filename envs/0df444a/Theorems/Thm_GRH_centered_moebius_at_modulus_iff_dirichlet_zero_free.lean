-- Prove2me | Theorems.Thm_GRH_centered_moebius_at_modulus_iff_dirichlet_zero_free
-- name    : GRH.centered_moebius_at_modulus_iff_dirichlet_zero_free
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-27T00:45:28.281311+00:00
-- url     : https://prove2.me/theorems/04e865ba-3dd7-43e6-9714-8e4d666e0b7c
-- title:
--   At a fixed modulus the centered Möbius bound is equivalent to Dirichlet zero-freeness
-- statement:
--   For every fixed q>0 the full exponent range of the exact centered Möbius bound in its unit classes is equivalent to the one-sided raw estimates at square cutoffs. Each condition is also equivalent to the zero-free right half-plane for every character modulo q, apart from the principal pole. Each implies ordinary RH.
-- source:
--   The target is GRH.centered_moebius_progression_bilinear_power_bound. The earlier square-cutoff reduction and the ordinary modulus-one case are posted on Prove2Me. The earlier modulus-one case is https://prove2.me/submissions/4965aba3-5ab0-4358-a9d3-9fc0714c6c2a .

import Definitions.Def_GRH_FactorialMoebius

open GRH.FactorialMoebius GRH.OneSidedMoebius

theorem GRH.centered_moebius_at_modulus_iff_dirichlet_zero_free (q : ℕ) [NeZero q] :
    (centered q ↔ ∀ θ : ℝ, 1/2 < θ → θ < 1 → upper q θ) ∧
    ((∀ θ : ℝ, 1/2 < θ → θ < 1 → upper q θ) ↔ rightHalfPlane q) ∧
    (rightHalfPlane q → RiemannHypothesis) := by sorry
