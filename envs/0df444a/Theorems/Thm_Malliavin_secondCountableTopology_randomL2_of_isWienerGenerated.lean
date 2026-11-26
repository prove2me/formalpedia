-- Prove2me | Theorems.Thm_Malliavin_secondCountableTopology_randomL2_of_isWienerGenerated
-- name    : Malliavin.secondCountableTopology_randomL2_of_isWienerGenerated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:09:08.147002+00:00
-- url     : https://prove2.me/theorems/da9fcb9e-08c3-5671-905c-ea1e5c3264fa
-- title:
--   Malliavin: second Countable Topology random L2 of is Wiener Generated
-- statement:
--   Consequently, the real ambient `L²` space is second-countable.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerChaos.lean#L348-L355
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerChaos.lean#L348-L355

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

theorem Malliavin.secondCountableTopology_randomL2_of_isWienerGenerated
    (hB : IsPreBrownianReal B P) (hgen : IsWienerGenerated B) :
    SecondCountableTopology (RandomL2 P) := by sorry
