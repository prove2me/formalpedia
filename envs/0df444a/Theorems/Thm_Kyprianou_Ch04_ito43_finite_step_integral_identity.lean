-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_finite_step_integral_identity
-- name    : Kyprianou.Ch04.ito43_finite_step_integral_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:25:43.893582+00:00
-- url     : https://prove2.me/theorems/f374003d-f318-5736-8672-36dd7676064c
-- title:
--   Finite threshold step integrates by its individual indicators
-- statement:
--   Distribute the finite sum against an integrable kernel, then restrict each measurable indicator set.
-- source:
--   Kyprianou (2006), Theorem 4.3 proof auxiliary

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.ito43_finite_step_integral_identity
    {α : Type} [MeasurableSpace α] (μ : Measure α) (S : Set α)
    (f : α → ℝ) (hf : IntegrableOn f S μ)
    (m : ℕ) (B : ℕ → Set α) (hB : ∀ i, MeasurableSet (B i)) (c : ℕ → ℝ) :
    let W : α → ℝ := fun x =>
      ∑ i ∈ Finset.range m, c i * (B i).indicator (fun _ => (1:ℝ)) x
    IntegrableOn (fun x => W x * f x) S μ ∧
      (∫ x in S, W x * f x ∂μ) =
        ∑ i ∈ Finset.range m, c i * (∫ x in B i ∩ S, f x ∂μ) := by sorry
