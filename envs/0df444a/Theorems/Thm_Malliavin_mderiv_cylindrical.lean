-- Prove2me | Theorems.Thm_Malliavin_mderiv_cylindrical
-- name    : Malliavin.mderiv_cylindrical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:05:01.757436+00:00
-- url     : https://prove2.me/theorems/f35ae1e4-f37f-5259-91ed-6f15e2aa8ced
-- title:
--   Malliavin: mderiv cylindrical
-- statement:
--   The classical formula: for a cylindrical functional `F x = f (L₁ x, …, Lₙ x)`,
--   `DF x = ∑ᵢ ∂ᵢ f (L x) • ofDual Lᵢ`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/MalliavinDerivative.lean#L366-L387
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/MalliavinDerivative.lean#L366-L387

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_MalliavinDerivative
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
open Malliavin
open CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  (μ : Measure W) [IsGaussian μ]

theorem Malliavin.mderiv_cylindrical {n : ℕ} (f : (Fin n → ℝ) → ℝ) (L : Fin n → StrongDual ℝ W)
    (x : W) (hf : DifferentiableAt ℝ f (fun i ↦ L i x)) :
    mderiv μ (fun y ↦ f (fun i ↦ L i y)) x =
      ∑ i, fderiv ℝ f (fun i ↦ L i x) (Pi.single i 1) • ofDual μ (L i) := by sorry
