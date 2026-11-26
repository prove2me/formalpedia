-- Prove2me | Theorems.Thm_Malliavin_isGaussianProcess_stepSum
-- name    : Malliavin.isGaussianProcess_stepSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:53:43.121067+00:00
-- url     : https://prove2.me/theorems/ddce0a51-bb53-4a33-bf26-09c976103044
-- title:
--   Malliavin: is Gaussian Process step Sum
-- statement:
--   Formal step sums are linear functionals of finitely many Brownian coordinates, hence form a
--   Gaussian process indexed by `ℝ≥0 →₀ ℝ`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L780-L786
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L780-L786

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_WienerIntegral
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
open CameronMartin

theorem Malliavin.isGaussianProcess_stepSum (hB : IsPreBrownianReal B P) :
    IsGaussianProcess (stepSum B) P := by sorry
