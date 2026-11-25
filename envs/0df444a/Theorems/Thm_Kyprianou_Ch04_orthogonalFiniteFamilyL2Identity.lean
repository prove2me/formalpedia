-- Prove2me | Theorems.Thm_Kyprianou_Ch04_orthogonalFiniteFamilyL2Identity
-- name    : Kyprianou.Ch04.orthogonalFiniteFamilyL2Identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T19:53:55.023145+00:00
-- url     : https://prove2.me/theorems/2b0270f0-26a8-5a97-aa49-974892f4d5a4
-- title:
--   Exact square-integral identity for finite orthogonal families
-- statement:
--   For a finite family of real integrable random variables whose pairwise products are integrable and whose distinct covariance products have expectation zero, the expectation of the square of their sum is the sum of their second moments.
-- source:
--   Finite-dimensional orthogonality identity used in Kyprianou (2006), Chapter 4, Exercise 4.4, to pass from diagonal and off-diagonal Poisson covariance identities to finite simple-integrand isometry.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
open MeasureTheory
open scoped BigOperators
set_option autoImplicit false
universe u v

theorem Kyprianou.Ch04.orthogonalFiniteFamilyL2Identity
    {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) {ι : Type v} [DecidableEq ι]
    (s : Finset ι) (Z : ι → Ω → ℝ)
    (hprod : ∀ i ∈ s, ∀ j ∈ s, Integrable (fun ω => Z i ω * Z j ω) P)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      ∫ ω, Z i ω * Z j ω ∂P = 0) :
    ∫ ω, (∑ i ∈ s, Z i ω) ^ 2 ∂P =
      ∑ i ∈ s, ∫ ω, (Z i ω) ^ 2 ∂P := by
  sorry
