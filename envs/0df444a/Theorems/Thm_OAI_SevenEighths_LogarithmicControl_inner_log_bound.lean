-- Prove2me | Theorems.Thm_OAI_SevenEighths_LogarithmicControl_inner_log_bound
-- name    : OAI.SevenEighths.LogarithmicControl.inner_log_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:23:03.884211+00:00
-- url     : https://prove2.me/theorems/cec53fa3-15d2-48f7-aa24-444f664b98b2
-- title:
--   Logarithmic Control: inner log bound
-- statement:
--   The Logarithmic Control construction uses the inner log bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/LogarithmicControl.lean#L330-L349
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/LogarithmicControl.lean#L330-L349

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

theorem OAI.SevenEighths.LogarithmicControl.inner_log_bound {g : ℂ → ℂ} {c : ℂ} {a e A M T : ℝ}
    (ha : 1 / 2 ≤ a) (ha' : a ≤ 1) (he : 0 < e) (he' : e < 1 / 1000)
    (hA : 1 ≤ A) (hM : 1 ≤ M) (hT : 1 ≤ T)
    (hg : DifferentiableOn ℂ g (ball c (2 - a - 2 * e)))
    (hRe : ∀ z ∈ ball c (2 - a - 3 * e), (g z).re ≤ M * T)
    (hin : ∀ z ∈ closedBall c (49 / 100), ‖g z‖ ≤ A)
    {z : ℂ} (hz : z ∈ closedBall c (2 - a - 6 * e)) :
    ‖g z‖ ≤ A * outerConstant e A M * T ^ uniformTheta e := by sorry
