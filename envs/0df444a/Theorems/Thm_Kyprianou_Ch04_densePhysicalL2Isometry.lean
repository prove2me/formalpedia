-- Prove2me | Theorems.Thm_Kyprianou_Ch04_densePhysicalL2Isometry
-- name    : Kyprianou.Ch04.densePhysicalL2Isometry
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:23:48.764459+00:00
-- url     : https://prove2.me/theorems/f3b2c476-ab37-4e1e-ab5a-9dde47dbc5b0
-- title:
--   densePhysicalL2Isometry
-- statement:
--   A physical map with a global L1 bound and almost-sure linearity inherits its L2 square identity from a dense submodule.
-- source:
--   Kyprianou (2006), Exercise 4.4, dense physical L2 extension.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
set_option autoImplicit false

/-- Extend a physical square-integral identity from a dense L2 submodule. -/
theorem Kyprianou.Ch04.densePhysicalL2Isometry
    {A Omega : Type} [MeasurableSpace A] [MeasurableSpace Omega]
    (mu : Measure A) [IsFiniteMeasure mu] (P : Measure Omega)
    (T : (A → ℝ) → Omega → ℝ)
    (hT : ∀ f g : A → ℝ, Measurable f → Measurable g →
      Integrable f mu → Integrable g mu →
      Integrable (T f) P ∧ Integrable (T g) P ∧
        (∫ w, |T f w - T g w| ∂P) ≤ 2 * ∫ a, |f a - g a| ∂mu)
    (hSub : ∀ f g : A → ℝ, Measurable f → Measurable g →
      Integrable f mu → Integrable g mu → T (f - g) =ᵐ[P] T f - T g)
    (R : Submodule ℝ (Lp ℝ 2 mu))
    (hDense : ∀ v : Lp ℝ 2 mu, v ∈ R.topologicalClosure)
    (hSq : ∀ v : Lp ℝ 2 mu, v ∈ R →
      Integrable (fun w => (T (v : A → ℝ) w)^2) P ∧
      (∫ w, (T (v : A → ℝ) w)^2 ∂P) = ∫ a, (v a)^2 ∂mu)
    (g : A → ℝ) (hgm : Measurable g) (hg : MemLp g 2 mu) :
    MemLp (T g) 2 P ∧ (∫ w, (T g w)^2 ∂P) = ∫ a, (g a)^2 ∂mu := by
  sorry
