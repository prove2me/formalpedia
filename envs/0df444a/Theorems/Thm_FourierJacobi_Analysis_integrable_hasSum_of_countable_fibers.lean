-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_integrable_hasSum_of_countable_fibers
-- name    : FourierJacobi.Analysis.integrable_hasSum_of_countable_fibers
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:40:17.046955+00:00
-- url     : https://prove2.me/theorems/29676f37-0c3f-4ce3-ab75-e845632c357f
-- title:
--   Analysis: integrable has Sum of countable fibers
-- statement:
--   The Analysis construction uses the integrable has Sum of countable fibers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/FiberIntegration.lean#L12-L38
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/FiberIntegration.lean#L12-L38

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Complex.Basic
import Definitions.Def_FourierJacobi_Analysis_FiberIntegration
set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open MeasureTheory

theorem FourierJacobi.Analysis.integrable_hasSum_of_countable_fibers {X ι : Type*}
    [MeasurableSpace X] [Countable ι] (μ : Measure X)
    (s : ι → Set X) (f : X → ℂ) (F : ι → ℂ)
    (hm : ∀ i, MeasurableSet (s i)) (hfinite : ∀ i, μ (s i) ≠ ⊤)
    (hd : Pairwise (fun i j => Disjoint (s i) (s j)))
    (hcover : (⋃ i, s i) =ᵐ[μ] Set.univ)
    (hvalue : ∀ i x, x ∈ s i → f x = F i)
    (hn : Summable (fun i => μ.real (s i) * ‖F i‖)) :
    Integrable f μ ∧ HasSum (fun i => (μ.real (s i) : ℂ) * F i) (∫ x, f x ∂μ) := by sorry
