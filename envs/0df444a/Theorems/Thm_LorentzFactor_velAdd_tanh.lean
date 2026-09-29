-- Prove2me | Theorems.Thm_LorentzFactor_velAdd_tanh
-- name    : LorentzFactor.velAdd_tanh
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T20:23:40.144958+00:00
-- url     : https://prove2.me/theorems/ba25c4bd-5599-4185-9101-df3b1f69e0d7
-- title:
--   Rapidity is additive under relativistic velocity addition
-- statement:
--   Relativistic velocity addition becomes ordinary addition in the rapidity variable: for all real rapidities $w_1, w_2$,
--
--   $$\frac{\tanh w_1 + \tanh w_2}{1 + \tanh w_1 \tanh w_2} = \tanh(w_1 + w_2).$$
--
--   This is the additivity of rapidity asserted in the source article — the property that makes the rapidity parameter, unlike the velocity, a one-parameter group.
-- source:
--   Lorentz factor, Wikipedia, revision oldid=1355686906, https://en.wikipedia.org/w/index.php?title=Lorentz_factor&oldid=1355686906

import Mathlib
import Definitions.Def_LorentzFactorDefs

open Filter Topology

namespace LorentzFactor

theorem velAdd_tanh (w₁ w₂ : ℝ) :
    velAdd (Real.tanh w₁) (Real.tanh w₂) = Real.tanh (w₁ + w₂) := by sorry

end LorentzFactor
