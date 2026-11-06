-- Prove2me | Theorems.Thm_OAI_SevenEighths_LogarithmicControl_log_eqOn_of_eq_center
-- name    : OAI.SevenEighths.LogarithmicControl.log_eqOn_of_eq_center
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:22:49.247937+00:00
-- url     : https://prove2.me/theorems/7e669412-5be9-4c3a-9218-9ae747f9cfb8
-- title:
--   Logarithmic Control: log eq On of eq center
-- statement:
--   The Logarithmic Control construction uses the log eq On of eq center property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/LogarithmicControl.lean#L66-L85
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/LogarithmicControl.lean#L66-L85

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

theorem OAI.SevenEighths.LogarithmicControl.log_eqOn_of_eq_center {g h : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hg : DifferentiableOn ℂ g (ball c r)) (hh : DifferentiableOn ℂ h (ball c r))
    (he : EqOn (Complex.exp ∘ g) (Complex.exp ∘ h) (ball c r)) (hc : g c = h c) :
    EqOn g h (ball c r) := by sorry
