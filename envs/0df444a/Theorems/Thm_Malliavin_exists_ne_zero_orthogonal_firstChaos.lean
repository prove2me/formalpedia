-- Prove2me | Theorems.Thm_Malliavin_exists_ne_zero_orthogonal_firstChaos
-- name    : Malliavin.exists_ne_zero_orthogonal_firstChaos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:53:43.742509+00:00
-- url     : https://prove2.me/theorems/238d1f62-c3ee-54d5-b587-c742c85e2ad3
-- title:
--   Malliavin: exists ne zero orthogonal first Chaos
-- statement:
--   **The first chaos and the constants do not exhaust `L²(P)`**: `(B 1 - B 0)(B 2 - B 1)` is a
--   nonzero centered element orthogonal to the first chaos.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L871-L884
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L871-L884

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_WienerIntegral
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem Malliavin.exists_ne_zero_orthogonal_firstChaos (hB : IsPreBrownianReal B P) :
    ∃ Y : RandomL2 P, Y ≠ 0 ∧ ∫ ω, Y ω ∂P = 0 ∧ ∀ Z ∈ firstChaos hB, ⟪Y, Z⟫_ℝ = 0 := by sorry
