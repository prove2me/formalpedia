-- Prove2me | Theorems.Thm_MeasureTheory_memLp_mul_left
-- name    : MeasureTheory.memLp_mul_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T03:10:45.071892+00:00
-- url     : https://prove2.me/theorems/b6ace642-447a-4fbf-86b8-9d88634f17e7
-- title:
--   Measure Theory: mem Lp mul left
-- statement:
--   The pointwise product `f • g` of an essentially bounded `f` with an
--   `L²` function `g` is again in `L²` (Hölder's inequality with exponents
--   `⊤, 2, 2`).
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Spectral/MultiplicationOperator.lean#L63-L67
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Spectral/MultiplicationOperator.lean#L63-L67

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

theorem MeasureTheory.memLp_mul_left {f : α → 𝕜} (hf : MemLp f ⊤ μ) (g : Lp 𝕜 2 μ) :
    MemLp (f • ⇑g) 2 μ := by sorry
