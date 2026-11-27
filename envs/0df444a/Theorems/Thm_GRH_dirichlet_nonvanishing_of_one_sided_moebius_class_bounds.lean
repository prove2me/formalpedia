-- Prove2me | Theorems.Thm_GRH_dirichlet_nonvanishing_of_one_sided_moebius_class_bounds
-- name    : GRH.dirichlet_nonvanishing_of_one_sided_moebius_class_bounds
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-27T00:45:19.82712+00:00
-- url     : https://prove2.me/theorems/3722eeed-8a98-5048-9397-5c35e807cbb0
-- title:
--   Dirichlet zero-freeness from one-sided square estimates at a fixed exponent
-- statement:
--   Assume ordinary RH. Fix q and 1/2 < θ < 1. If every unit residue has a raw one-sided Möbius upper bound of exponent θ at all squares, then every character modulo q has nonvanishing L-function for Re(s)>θ with the principal pole excluded.
-- source:
--   The target is GRH.centered_moebius_progression_bilinear_power_bound. The earlier square-cutoff reduction and the ordinary modulus-one case are posted on Prove2Me. The analytic continuation of ordered partial sums is https://prove2.me/theorems/557f3b52-774c-43a5-85ec-93534ddbe38c .

import Definitions.Def_GRH_FactorialMoebius

open GRH.FactorialMoebius GRH.OneSidedMoebius

theorem GRH.dirichlet_nonvanishing_of_one_sided_moebius_class_bounds (hRH : RiemannHypothesis) (q : ℕ) [NeZero q] (θ : ℝ)
    (hl : 1/2 < θ) (hr : θ < 1) (h : upper q θ) :
    ∀ (χ : DirichletCharacter ℂ q) (s : ℂ), θ < s.re → ¬ (χ=1 ∧ s=1) → χ.LFunction s ≠ 0 := by sorry
