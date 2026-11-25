-- Prove2me | Theorems.Thm_MeasureTheory_mulL2_isSelfAdjoint
-- name    : MeasureTheory.mulL2_isSelfAdjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T03:11:14.948593+00:00
-- url     : https://prove2.me/theorems/7773d117-8b09-4c09-ab9f-97fe7b1aa12f
-- title:
--   Measure Theory: mul L2 is Self Adjoint
-- statement:
--   **Self-adjointness.** If the symbol `f` is real-valued (a.e. fixed by
--   complex conjugation), then `M_f` is self-adjoint. In particular an indicator
--   symbol gives a self-adjoint operator; together with `mulL2_mul`
--   (`M_𝟙 ∘ M_𝟙 = M_{𝟙·𝟙} = M_𝟙`) this makes `M_𝟙` an orthogonal projection.
--
--   The proof is the pointwise Hölder identity for the `L²` inner product:
--   `⟪f • x, y⟫ = ∫ conj(f) ⟪x, y⟫` and `⟪x, f • y⟫ = ∫ f ⟪x, y⟫`, equal when
--   `conj f = f`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Spectral/MultiplicationOperator.lean#L126-L138
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Spectral/MultiplicationOperator.lean#L126-L138

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

theorem MeasureTheory.mulL2_isSelfAdjoint (f : α → 𝕜) (hf : MemLp f ⊤ μ)
    (hreal : ∀ᵐ a ∂μ, (starRingEnd 𝕜) (f a) = f a) :
    IsSelfAdjoint (mulL2 f hf) := by sorry
