-- Prove2me | Theorems.Thm_Malliavin_wienerChaos_coordinate_eq_projection
-- name    : Malliavin.wienerChaos_coordinate_eq_projection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:08:51.818661+00:00
-- url     : https://prove2.me/theorems/4f34559b-2c2a-545b-bcfd-89e6518ba771
-- title:
--   Malliavin: wiener Chaos coordinate eq projection
-- statement:
--   Hilbert-sum coordinates are the orthogonal projections onto each selected subspace.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerChaos.lean#L495-L516
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerChaos.lean#L495-L516

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

theorem Malliavin.wienerChaos_coordinate_eq_projection
    (hB : IsPreBrownianReal B P)
    (hsum : IsHilbertSum ℝ
      (fun n : ℕ => ↥(homogeneousChaos hB n : Submodule ℝ (RandomL2 P)))
      (fun n : ℕ => (homogeneousChaos hB n : Submodule ℝ (RandomL2 P)).subtypeₗᵢ))
    (n : ℕ) (F : RandomL2 P) :
    hsum.linearIsometryEquiv F n =
      (homogeneousChaos hB n : Submodule ℝ (RandomL2 P)).orthogonalProjectionOnto F := by sorry
