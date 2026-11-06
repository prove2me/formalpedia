-- Prove2me | Theorems.Thm_OAI_SevenEighths_LogarithmicControl_logarithmic_control
-- name    : OAI.SevenEighths.LogarithmicControl.logarithmic_control
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:53:21.511464+00:00
-- url     : https://prove2.me/theorems/4636708a-d1f1-4d25-8f1f-7b99460a4b70
-- title:
--   Logarithmic Control: logarithmic control
-- statement:
--   The Logarithmic Control construction uses the logarithmic control property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/LogarithmicControl.lean#L419-L465
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/LogarithmicControl.lean#L419-L465

import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_OAI_NumberTheory_DirichletL_LogarithmicControl
set_option autoImplicit false
open OAI
noncomputable section
open scoped Classical Topology
open Set Filter Metric Complex
open OAI.SevenEighths OAI.SevenEighths.LogarithmicControl

theorem OAI.SevenEighths.LogarithmicControl.logarithmic_control {e A M ε : ℝ}
    (he : 0 < e) (he' : e < 1 / 1000) (hA : 1 ≤ A) (hM : 1 ≤ M) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ (a C : ℝ) (L E : ℂ → ℂ) (c : ℂ),
      1 / 2 ≤ a → a ≤ 1 → Real.exp 1 ≤ C →
      DifferentiableOn ℂ L (ball c (2 - a - 2 * e)) →
      (∀ z ∈ ball c (2 - a - 2 * e), L z ≠ 0) →
      (∀ z ∈ ball c (2 - a - 3 * e), ‖L z‖ ≤ C ^ M) →
      DifferentiableOn ℂ E (ball c (1 / 2)) →
      EqOn (Complex.exp ∘ E) L (ball c (1 / 2)) →
      (∀ z ∈ closedBall c (49 / 100), ‖E z‖ ≤ A) →
      (∀ z ∈ closedBall c (2 - a - 6 * e), ‖L z‖ + ‖(L z)⁻¹‖ ≤ D * C ^ ε) ∧
      (∀ z ∈ closedBall c (2 - a - 8 * e),
        ‖deriv L z / L z‖ ≤ (outerConstant e A M / (2 * e)) * Real.log C) := by sorry
