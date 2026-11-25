-- Prove2me | Theorems.Thm_Kyprianou_Ch04_signedWeightSquarePolarization
-- name    : Kyprianou.Ch04.signedWeightSquarePolarization
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T21:54:51.627061+00:00
-- url     : https://prove2.me/theorems/0a84962e-023d-4227-9dae-30163cf4419f
-- title:
--   Signed-weight polarisation for additive second moments
-- statement:
--   If the sum of two real random variables has a weighted second moment equal to the sum of their weighted second moments, the signed weighted cross moment vanishes, assuming integrability of the three weighted squares.
-- source:
--   Polarisation of a quadratic form; Kyprianou Chapter 4 Exercise 4.4.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
open MeasureTheory Filter
set_option autoImplicit false
universe u

theorem Kyprianou.Ch04.signedWeightSquarePolarization
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (W A B C : Ω → ℝ)
    (hA : Integrable (fun ω => W ω * (A ω)^2) P)
    (hB : Integrable (fun ω => W ω * (B ω)^2) P)
    (hC : Integrable (fun ω => W ω * (C ω)^2) P)
    (hAdd : C =ᵐ[P] (fun ω => A ω + B ω))
    (hVar : (∫ ω, W ω * (C ω)^2 ∂P) =
      (∫ ω, W ω * (A ω)^2 ∂P) + (∫ ω, W ω * (B ω)^2 ∂P)) :
    (∫ ω, W ω * A ω * B ω ∂P) = 0 := by
  sorry
