-- Prove2me | Theorems.Thm_GRH_principal_moebius_upper_excludes_zeta_zeros_at_any_modulus
-- name    : GRH.principal_moebius_upper_excludes_zeta_zeros_at_any_modulus
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-27T00:45:24.248933+00:00
-- url     : https://prove2.me/theorems/5406cd9a-b201-4700-8e8b-0c995da709d9
-- title:
--   One-sided coprime Möbius sums at any modulus exclude ordinary zeta zeros
-- statement:
--   For a positive modulus q and 1/2 ≤ θ < 1, upper bounds at square cutoffs in all reduced classes give an upper bound of order (n+1)^θ for the coprime Möbius sum. That one-sided coprime estimate alone excludes zeros of the Riemann zeta function in Re(s)>θ away from 1.
-- source:
--   The target is GRH.centered_moebius_progression_bilinear_power_bound. The earlier square-cutoff reduction and the ordinary modulus-one case are posted on Prove2Me. The principal-character regularization uses Mathlib. The Landau continuation is https://prove2.me/submissions/7aff1eb5-055e-42bb-9c07-594cb9345051 and the earlier ordinary argument is https://prove2.me/submissions/1099a03e-7783-4816-850e-06286c0f68bd .

import Definitions.Def_GRH_FactorialMoebius

open GRH.FactorialMoebius GRH.OneSidedMoebius

theorem GRH.principal_moebius_upper_excludes_zeta_zeros_at_any_modulus (q : ℕ) [NeZero q] (θ : ℝ) (hl : 1/2 ≤ θ) (hr : θ < 1) :
    (upper q θ → principalUpper q θ) ∧
    (principalUpper q θ → ∀ s : ℂ, θ < s.re → s ≠ 1 → riemannZeta s ≠ 0) := by sorry
