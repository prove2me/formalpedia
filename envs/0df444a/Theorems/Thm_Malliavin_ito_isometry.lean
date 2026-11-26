-- Prove2me | Theorems.Thm_Malliavin_ito_isometry
-- name    : Malliavin.ito_isometry
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T10:58:17.361729+00:00
-- url     : https://prove2.me/theorems/b9bf647e-4607-4ef8-add4-dbd23de651a3
-- title:
--   Malliavin: ito isometry
-- statement:
--   **Itô isometry** for step integrals:
--   `E[I a * I b] = ∑ aᵢ bᵢ (t_{i+1} - t_i)`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/IteratedIntegral.lean#L232-L321
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/IteratedIntegral.lean#L232-L321

import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Definitions.Def_Malliavin_Simplex
import Mathlib.Probability.BrownianMotion.Basic
import Definitions.Def_Malliavin_IteratedIntegral
set_option autoImplicit false
open Malliavin
open MeasureTheory
open scoped NNReal
universe u_1 u_2 u_3 u_4 u_7 u_8
universe u₁ u₂ u₃ u₄ u₅
variable {Ω : Type*} [MeasureSpace Ω]
variable {W : ℝ≥0 → Ω → ℝ}

theorem Malliavin.ito_isometry (hW : IsWienerCov W) {n : ℕ} (P : Partition n) (a b : Fin n → ℝ) :
    ∫ x, stepIntegral W P a x * stepIntegral W P b x
      = ∑ i : Fin n, a i * b i * ((P.t i.succ : ℝ) - (P.t i.castSucc : ℝ)) := by sorry
