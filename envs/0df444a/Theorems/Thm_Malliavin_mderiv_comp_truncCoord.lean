-- Prove2me | Theorems.Thm_Malliavin_mderiv_comp_truncCoord
-- name    : Malliavin.mderiv_comp_truncCoord
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:19:14.994104+00:00
-- url     : https://prove2.me/theorems/9a04b2d2-1341-561c-836f-b72be6c4ba6b
-- title:
--   Malliavin: mderiv comp trunc Coord
-- statement:
--   **Chain rule for truncated cylindrical functionals**.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CylindricalGrowth.lean#L179-L195
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CylindricalGrowth.lean#L179-L195

import Definitions.Def_Malliavin_DualDerivative
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Definitions.Def_Malliavin_CylindricalGrowth
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
open CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  (μ : Measure W) [IsGaussian μ]

theorem Malliavin.mderiv_comp_truncCoord {n : ℕ} (f : (Fin n → ℝ) → ℝ) (hf : ContDiff ℝ 1 f) (m : ℕ)
    (L : Fin n → StrongDual ℝ W) (x : W) :
    mderiv μ (fun y ↦ f (truncCoord m L y)) x =
      ∑ i, (fderiv ℝ f (truncCoord m L x) (Pi.single i 1) * deriv (cutoff m) (L i x)) •
        ofDual μ (L i) := by sorry
