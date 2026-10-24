-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_real_constant_div_tends_zero
-- name    : OAI.PiExponent.DeterminantContradiction.real_constant_div_tends_zero
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T18:05:06.068875+00:00
-- url     : https://prove2.me/theorems/baf3e1f9-328a-4ac5-8a03-518d5578629d
-- title:
--   A fixed constant divided by H tends to zero
-- statement:
--   For every fixed real constant c, c/H tends to zero as H tends to positive infinity.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology

theorem OAI.PiExponent.DeterminantContradiction.real_constant_div_tends_zero (c : Real) : Tendsto (fun H : Real => c / H) atTop (𝓝 0) := by sorry
