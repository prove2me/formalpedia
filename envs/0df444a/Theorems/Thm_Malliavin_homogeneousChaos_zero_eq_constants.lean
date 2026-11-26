-- Prove2me | Theorems.Thm_Malliavin_homogeneousChaos_zero_eq_constants
-- name    : Malliavin.homogeneousChaos_zero_eq_constants
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:10:00.438887+00:00
-- url     : https://prove2.me/theorems/f4c7c704-de1e-4bbd-a487-d98588e0982b
-- title:
--   Malliavin: homogeneous Chaos zero eq constants
-- statement:
--   The selected zeroth homogeneous subspace is exactly the subspace of constants.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerChaos.lean#L104-L128
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerChaos.lean#L104-L128

import Definitions.Def_Malliavin_MultipleIntegral
import Definitions.Def_Malliavin_WienerChaos
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Topology symmDiff
noncomputable section
open Malliavin
universe u v u_1 u_2 u_4 u_6
universe u₁ u₂ u₃
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ}
set_option linter.style.haveILetI false

theorem Malliavin.homogeneousChaos_zero_eq_constants (hB : IsPreBrownianReal B P) :
    letI : IsProbabilityMeasure P := (hB.hasLaw ∅).isProbabilityMeasure
    (homogeneousChaos hB 0 : Submodule ℝ (RandomL2 P)) = constantRandomVariables P := by sorry
