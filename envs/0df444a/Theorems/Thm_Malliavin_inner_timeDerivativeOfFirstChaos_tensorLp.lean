-- Prove2me | Theorems.Thm_Malliavin_inner_timeDerivativeOfFirstChaos_tensorLp
-- name    : Malliavin.inner_timeDerivativeOfFirstChaos_tensorLp
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:28:58.602442+00:00
-- url     : https://prove2.me/theorems/f37734d3-1b81-5d1a-b4b8-9cefcb7d23c4
-- title:
--   Malliavin: inner time Derivative Of First Chaos tensor Lp
-- statement:
--   **Weak Fubini identity for the time derivative**:
--   `⟪Dₜ U, g ⊗ 1_A⟫ = ∫ ω in A, ⟪J₁ g, U ω⟫ ∂P`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/TimeDerivative.lean#L194-L203
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/TimeDerivative.lean#L194-L203

import Definitions.Def_Malliavin_WienerIntegral
import Definitions.Def_Malliavin_FubiniLift
import Definitions.Def_Malliavin_MalliavinDerivative
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_TimeDerivative
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} [SFinite P]

theorem Malliavin.inner_timeDerivativeOfFirstChaos_tensorLp (hB : IsPreBrownianReal B P)
    (U : Lp (firstChaos hB) 2 P) (A : FiniteMeasurableSet P)
    (g : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    ⟪timeDerivativeOfFirstChaos hB U, tensorLp A g⟫_ℝ =
      ∫ ω in A.1, ⟪wienerIntegral hB g, (U ω : RandomL2 P)⟫_ℝ ∂P := by sorry
