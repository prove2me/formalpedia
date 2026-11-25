-- Prove2me | Theorems.Thm_MeasureTheory_mulL2_one
-- name    : MeasureTheory.mulL2_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T03:11:02.986722+00:00
-- url     : https://prove2.me/theorems/a057fc1f-e1df-5c66-9db1-5a75fcbf4e5f
-- title:
--   Measure Theory: mul L2 one
-- statement:
--   **Unitality.** `M_1` is the identity operator.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Spectral/MultiplicationOperator.lean#L111-L116
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Spectral/MultiplicationOperator.lean#L111-L116

module
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Function.Holder
public import Definitions.Def_BasicResults_Spectral_MultiplicationOperator
set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal NNReal
open MeasureTheory
open MeasureTheory
variable {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
variable {𝕜 : Type*} [RCLike 𝕜]

theorem MeasureTheory.mulL2_one (h1 : MemLp (1 : α → 𝕜) ⊤ μ) :
    mulL2 (1 : α → 𝕜) h1 = ContinuousLinearMap.id 𝕜 (Lp 𝕜 2 μ) := by sorry
