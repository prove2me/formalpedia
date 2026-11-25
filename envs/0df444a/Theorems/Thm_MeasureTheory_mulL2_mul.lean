-- Prove2me | Theorems.Thm_MeasureTheory_mulL2_mul
-- name    : MeasureTheory.mulL2_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T03:10:49.395395+00:00
-- url     : https://prove2.me/theorems/b41c71ed-37a0-5dac-ae5e-7945ee43be9b
-- title:
--   Measure Theory: mul L2 mul
-- statement:
--   **Multiplicativity.** `M_f ∘ M_g = M_{f g}`: multiplication operators
--   compose by multiplying their symbols.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Spectral/MultiplicationOperator.lean#L101-L108
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Spectral/MultiplicationOperator.lean#L101-L108

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

theorem MeasureTheory.mulL2_mul (f g : α → 𝕜) (hf : MemLp f ⊤ μ) (hg : MemLp g ⊤ μ) :
    (mulL2 f hf).comp (mulL2 g hg) = mulL2 (f * g) (memLp_mul_top hf hg) := by sorry
