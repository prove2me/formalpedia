-- Prove2me | Theorems.Thm_Malliavin_hasSum_wienerChaos
-- name    : Malliavin.hasSum_wienerChaos
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:10:47.575421+00:00
-- url     : https://prove2.me/theorems/2fcf3b5e-3d12-42b7-a1d1-2d6808b9efed
-- title:
--   Malliavin: has Sum wiener Chaos
-- statement:
--   Every square-integrable functional is the convergent sum of the coordinates canonical
--   relative to the selected subspaces whenever the totality contract holds.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerChaos.lean#L566-L574
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerChaos.lean#L566-L574

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

theorem Malliavin.hasSum_wienerChaos (hB : IsPreBrownianReal B P) (htotal : IsWienerTotal hB)
    (F : RandomL2 P) :
    HasSum
      (fun n : ℕ =>
        ((wienerChaosEquiv hB htotal F) n).1)
      F := by sorry
