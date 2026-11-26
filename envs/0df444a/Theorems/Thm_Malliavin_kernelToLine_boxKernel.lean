-- Prove2me | Theorems.Thm_Malliavin_kernelToLine_boxKernel
-- name    : Malliavin.kernelToLine_boxKernel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:50:53.855308+00:00
-- url     : https://prove2.me/theorems/6564cbd4-5edc-4582-8639-518e437109cf
-- title:
--   Malliavin: kernel To Line box Kernel
-- statement:
--   The Malliavin construction uses the kernel To Line box Kernel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L500-L511
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L500-L511

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_WienerIntegral
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem Malliavin.kernelToLine_boxKernel {a b : ℝ≥0} :
    kernelToLine (boxKernel (fun _ : Fin 1 ↦ a) (fun _ ↦ b)) =
      indicatorConstLp 2 measurableSet_Ioc (nonnegativeLebesgueMeasure_Ioc_ne_top a b) (1 : ℝ) := by sorry
