-- Prove2me | Theorems.Thm_Malliavin_fubiniLift_boundedSMul
-- name    : Malliavin.fubiniLift_boundedSMul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:54:13.254853+00:00
-- url     : https://prove2.me/theorems/0756abc6-6f12-58ac-8bd4-908f72d25062
-- title:
--   Malliavin: fubini Lift bounded SMul
-- statement:
--   **The Fubini lift commutes with multiplication by bounded functions of `ω`**:
--   `fubiniLift (G • U) = (G ∘ snd) • fubiniLift U`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/FubiniLift.lean#L748-L791
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/FubiniLift.lean#L748-L791

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_FubiniLift
set_option autoImplicit false
open MeasureTheory Filter Topology Function
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3
open Malliavin
variable {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T] {μ : Measure Ω} {ν : Measure T}
  [SFinite μ] [SFinite ν]

theorem Malliavin.fubiniLift_boundedSMul {G : Ω → ℝ} (hG : AEStronglyMeasurable G μ) {C : ℝ}
    (hC : ∀ x, |G x| ≤ C) (U : Lp (Lp ℝ 2 ν) 2 μ) :
    fubiniLift (boundedSMul hG hC U) =
      boundedSMul (aestronglyMeasurable_comp_snd (ν := ν) hG) (fun p ↦ hC p.2) (fubiniLift U) := by sorry
