-- Prove2me | Theorems.Thm_OAI_SevenEighths_LogarithmicControl_differentiableOn_of_exp_eq
-- name    : OAI.SevenEighths.LogarithmicControl.differentiableOn_of_exp_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:22:44.570047+00:00
-- url     : https://prove2.me/theorems/30f9a045-6a04-47dd-922e-966dea53778b
-- title:
--   Logarithmic Control: differentiable On of exp eq
-- statement:
--   The Logarithmic Control construction uses the differentiable On of exp eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/LogarithmicControl.lean#L18-L35
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/LogarithmicControl.lean#L18-L35

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

theorem OAI.SevenEighths.LogarithmicControl.differentiableOn_of_exp_eq {U : Set ℂ} (hU : IsOpen U)
    {L g : ℂ → ℂ} (hL : DifferentiableOn ℂ L U)
    (hg : ContinuousOn g U) (he : EqOn (Complex.exp ∘ g) L U) :
    DifferentiableOn ℂ g U := by sorry
