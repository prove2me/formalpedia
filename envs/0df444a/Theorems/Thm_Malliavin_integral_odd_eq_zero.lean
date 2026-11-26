-- Prove2me | Theorems.Thm_Malliavin_integral_odd_eq_zero
-- name    : Malliavin.integral_odd_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:50:55.108799+00:00
-- url     : https://prove2.me/theorems/01cce304-5b50-5d2d-a135-e69fb212ed75
-- title:
--   Malliavin: integral odd eq zero
-- statement:
--   **Symmetry of a pre-Brownian process.**  The finite-dimensional laws are invariant under
--   `B ↦ -B`, so the Bochner integral of an odd measurable function of finitely many coordinates
--   vanishes.  No integrability hypothesis is needed for this formal statement because Lean's
--   Bochner integral is zero by convention in the nonintegrable case.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L594-L605
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L594-L605

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_WienerIntegral
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem Malliavin.integral_odd_eq_zero (hB : IsPreBrownianReal B P) (I : Finset ℝ≥0)
    {f : (I → ℝ) → ℝ} (hf : Measurable f) (hodd : ∀ x, f (-x) = -f x) :
    ∫ ω, f (I.restrict (B · ω)) ∂P = 0 := by sorry
