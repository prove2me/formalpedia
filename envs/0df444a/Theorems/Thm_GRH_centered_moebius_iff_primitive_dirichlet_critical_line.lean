-- Prove2me | Theorems.Thm_GRH_centered_moebius_iff_primitive_dirichlet_critical_line
-- name    : GRH.centered_moebius_iff_primitive_dirichlet_critical_line
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-27T00:45:22.160999+00:00
-- url     : https://prove2.me/theorems/c1d44979-caf5-5cb6-9538-670c36351920
-- title:
--   The all-moduli centered Möbius estimate is equivalent to the primitive Dirichlet critical-line conjecture
-- statement:
--   The requested simultaneous centered Möbius power estimate holds exactly when every zero of every primitive Dirichlet L-function in the open critical strip has real part one half.
-- source:
--   The target is GRH.centered_moebius_progression_bilinear_power_bound. The earlier square-cutoff reduction and the ordinary modulus-one case are posted on Prove2Me. The primitive critical-line and right-half-plane formulations are related by https://prove2.me/theorems/6079bb22-1b0f-4fd6-b467-4b227db03fca .

import Definitions.Def_GRH_FactorialMoebius

open GRH.FactorialMoebius GRH.OneSidedMoebius

theorem GRH.centered_moebius_iff_primitive_dirichlet_critical_line : centeredBound ↔
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      ∀ s : ℂ, 0 < s.re → s.re < 1 → χ.LFunction s = 0 → s.re = 1/2 := by sorry
