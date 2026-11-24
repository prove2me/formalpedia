-- Prove2me | Theorems.Thm_Kyprianou_Ch02_aeBVUniformGridAbsoluteSumsBoundedV1
-- name    : Kyprianou.Ch02.aeBVUniformGridAbsoluteSumsBoundedV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:47:26.389468+00:00
-- url     : https://prove2.me/theorems/f114192e-a8db-49fb-a780-e3c41440a556
-- title:
--   Locally BV paths bound all uniform unit-horizon absolute increment sums
-- statement:
--   Use the finite Mathlib eVariationOn of the compact unit interval for each BV path. Clip the uniform mesh sequence at the final grid point, apply the finite variation sum bound and convert from ENNReal distances to real absolute sums. This result does not require any Lévy or probability assumption.
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.12, bounded-variation Lévy paths and Lévy-triplet characterisation.

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch02.aeBVUniformGridAbsoluteSumsBoundedV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ≥0 → Ω → ℝ)
    (hBV : ∀ᵐ ω ∂P, LocallyBoundedVariationOn
      (fun t : ℝ≥0 => X t ω) Set.univ) :
    ∀ᵐ ω ∂P, ∃ B : ℝ, ∀ n : ℕ,
      (∑ i : Fin (n + 1),
          |X (((i.val + 1 : ℕ) : ℝ≥0) * (((n : ℝ≥0) + 1)⁻¹)) ω -
           X ((i.val : ℝ≥0) * (((n : ℝ≥0) + 1)⁻¹)) ω|) ≤ B := by
  sorry
