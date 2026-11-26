-- Prove2me | Theorems.Thm_Malliavin_inner_brownianLp_unitIncrementLp
-- name    : Malliavin.inner_brownianLp_unitIncrementLp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:54:01.216588+00:00
-- url     : https://prove2.me/theorems/9ce3b950-e5bf-5e22-8955-251d71c3ad4d
-- title:
--   Malliavin: inner brownian Lp unit Increment Lp
-- statement:
--   The Malliavin construction uses the inner brownian Lp unit Increment Lp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L986-L991
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L986-L991

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_WienerIntegral
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem Malliavin.inner_brownianLp_unitIncrementLp (hB : IsPreBrownianReal B P) (t : ℝ≥0) (k : ℕ) :
    ⟪brownianLp hB t, unitIncrementLp hB k⟫_ℝ = min (t : ℝ) (k + 1) - min (t : ℝ) k := by sorry
