-- Prove2me | Theorems.Thm_Kyprianou_Ch04_finiteFamilyCovarianceExpansion
-- name    : Kyprianou.Ch04.finiteFamilyCovarianceExpansion
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:25:04.768536+00:00
-- url     : https://prove2.me/theorems/5e1097f5-9a2a-50e8-bdda-39494d241189
-- title:
--   Second-moment expansion of a finite family
-- statement:
--   Expand the squared finite sum as a double sum and apply finite-sum integral linearity under pairwise product integrability.
-- source:
--   Kyprianou Chapter 4 Exercise 4.4; covariance expansion.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
open MeasureTheory
open scoped BigOperators
set_option autoImplicit false
universe u v

theorem Kyprianou.Ch04.finiteFamilyCovarianceExpansion
    {Ω : Type u} {ι : Type v} [MeasurableSpace Ω] [DecidableEq ι]
    (P : Measure Ω) (s : Finset ι) (Z : ι → Ω → ℝ)
    (hprod : ∀ i ∈ s, ∀ j ∈ s,
      Integrable (fun ω => Z i ω * Z j ω) P) :
    (∫ ω, (∑ i ∈ s, Z i ω)^2 ∂P) =
      ∑ i ∈ s, ∑ j ∈ s, ∫ ω, Z i ω * Z j ω ∂P := by
  sorry
