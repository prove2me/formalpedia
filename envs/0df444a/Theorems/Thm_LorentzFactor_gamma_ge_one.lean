-- Prove2me | Theorems.Thm_LorentzFactor_gamma_ge_one
-- name    : LorentzFactor.gamma_ge_one
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T19:38:32.188157+00:00
-- url     : https://prove2.me/theorems/5679599b-a10e-4468-b6b9-a5b149ac08bf
-- title:
--   $\gamma \ge 1$, with equality exactly at rest
-- statement:
--   For every subluminal velocity ratio $\beta$ with $|\beta| < 1$, the Lorentz factor satisfies $\gamma(\beta) \ge 1$, and $\gamma(\beta) = 1$ holds if and only if $\beta = 0$. This is the first line of the numerical table of the source article: time dilation and length contraction are never in the opposite direction, and they are absent exactly for an observer at rest relative to the object.
-- source:
--   Lorentz factor, Wikipedia, revision oldid=1355686906, https://en.wikipedia.org/w/index.php?title=Lorentz_factor&oldid=1355686906

import Mathlib
import Definitions.Def_LorentzFactorDefs

open Filter Topology

namespace LorentzFactor

theorem gamma_ge_one (β : ℝ) (h : |β| < 1) :
    1 ≤ gamma β ∧ (gamma β = 1 ↔ β = 0) := by sorry

end LorentzFactor
