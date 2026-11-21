-- Prove2me | Theorems.Thm_MasulloRH_regularized_spectral_domination_any_window
-- name    : MasulloRH.regularized_spectral_domination_any_window
-- status  : Proved
-- author  : @Abhishek Anand
-- created : 2026-11-20T23:30:07.448646+00:00
-- url     : https://prove2.me/theorems/a3b02907-13fe-47a2-9063-5dce973e6b57
-- title:
--   Uniform spectral cutoff bound for every trace window
-- statement:
--   Fix $s$ with $\Re(s)>3/2$. For each real half-width $\alpha$, the cutoff Mellin terms at all included critical zeros are bounded, uniformly in the cutoff, by a constant times the zero multiplicity divided by $1+(\Im\rho)^2$. This includes the full critical strip at $\alpha=1/2$.
-- source:
--   Endpoint extension of Prove2Me theorem MasulloRH.regularized_spectral_domination (3885a04c-8332-4022-8035-11d5bacaf1d2), using the same two integrations by parts.

import Definitions.Def_MasulloRH_RegularizedTrace
open MasulloRH

theorem MasulloRH.regularized_spectral_domination_any_window (α : ℝ)
    (s : ℂ) (hs : (3 / 2 : ℝ) < s.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (ρ : ZetaZerosInTraceStrip α),
      ‖zetaTraceTerm (regularizedTraceTest n s) α ρ‖ ≤ C * zeroDecayWeight α ρ := by sorry
