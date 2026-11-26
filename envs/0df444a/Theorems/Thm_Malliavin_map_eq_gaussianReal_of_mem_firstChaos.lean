-- Prove2me | Theorems.Thm_Malliavin_map_eq_gaussianReal_of_mem_firstChaos
-- name    : Malliavin.map_eq_gaussianReal_of_mem_firstChaos
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:03:57.281501+00:00
-- url     : https://prove2.me/theorems/ed70892c-833f-44d5-8ae1-33b1425fed0c
-- title:
--   Malliavin: map eq gaussian Real of mem first Chaos
-- statement:
--   Every first-chaos element has the centered Gaussian law whose variance is its squared
--   `L²(P)` norm.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L935-L941
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L935-L941

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_WienerIntegral
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem Malliavin.map_eq_gaussianReal_of_mem_firstChaos (hB : IsPreBrownianReal B P) {Z : RandomL2 P}
    (hZ : Z ∈ firstChaos hB) : P.map Z = gaussianReal 0 (‖Z‖₊ ^ 2) := by sorry
