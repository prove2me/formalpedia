-- Prove2me | Theorems.Thm_MeasureTheory_mulL2_coeFn
-- name    : MeasureTheory.mulL2_coeFn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:19:22.515627+00:00
-- url     : https://prove2.me/theorems/f735d086-5b75-415c-b819-5a3f7091b8b6
-- title:
--   Measure Theory: mul L2 coe Fn
-- statement:
--   **Defining identity.** As an a.e. function, `M_f g` is `f • g`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Spectral/MultiplicationOperator.lean#L77-L81
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Spectral/MultiplicationOperator.lean#L77-L81

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

theorem MeasureTheory.mulL2_coeFn (f : α → 𝕜) (hf : MemLp f ⊤ μ) (g : Lp 𝕜 2 μ) :
    ⇑(mulL2 f hf g) =ᵐ[μ] f • ⇑g := by sorry
