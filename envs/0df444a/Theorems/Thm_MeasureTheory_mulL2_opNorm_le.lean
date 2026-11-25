-- Prove2me | Theorems.Thm_MeasureTheory_mulL2_opNorm_le
-- name    : MeasureTheory.mulL2_opNorm_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T03:10:48.987414+00:00
-- url     : https://prove2.me/theorems/83835fce-b37b-4d67-b3a5-94efd8443b30
-- title:
--   Measure Theory: mul L2 op Norm le
-- statement:
--   **Operator-norm bound.** `‖M_f‖ ≤ ‖f‖∞` (the essential supremum of `f`).
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Spectral/MultiplicationOperator.lean#L84-L92
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Spectral/MultiplicationOperator.lean#L84-L92

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

theorem MeasureTheory.mulL2_opNorm_le (f : α → 𝕜) (hf : MemLp f ⊤ μ) :
    ‖mulL2 f hf‖ ≤ (eLpNorm f ⊤ μ).toReal := by sorry
