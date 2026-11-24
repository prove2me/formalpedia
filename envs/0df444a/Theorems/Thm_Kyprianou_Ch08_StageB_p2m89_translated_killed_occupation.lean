-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m89_translated_killed_occupation
-- name    : Kyprianou.Ch08.StageB.p2m89_translated_killed_occupation
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T08:18:52.655951+00:00
-- url     : https://prove2.me/theorems/1f8ebc50-22cb-4f98-90db-c63cad9f5f2c
-- title:
--   Translated half-line killed occupation identity
-- statement:
--   Translate the proved half-line kernel at starting capital n to the destination coordinate y, using translation invariance of Lebesgue measure.
-- source:
--   Kyprianou (2006), Corollary 8.9; corrected occupation identity 33cf8321-6b73-409d-84cc-a8da6fcb2949.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

open Kyprianou.Ch08 Kyprianou.Ch08.StageB Topology

theorem Kyprianou.Ch08.StageB.p2m89_translated_killed_occupation
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (hW : HasSourceScaleFamily ψ W) (q : ℝ) (hq : 0 < q) (x : ℝ) (A : Set ℝ) (hA : MeasurableSet A) (n : ℕ) :
    (∫⁻ y in A, if 0 ≤ y + (n : ℝ) - x then
      ENNReal.ofReal (Real.exp (-(Phi ψ q) * (y - x)) *
        (Real.exp (-(Phi ψ q) * (n : ℝ)) * W q n) - W q (x - y))
      else 0) = (∫⁻ t : ℝ≥0, ENNReal.ofReal (Real.exp (-q * (t : ℝ))) *
      P {ω | (t : WithTop ℝ≥0) < tauMinus (shifted D.X (n : ℝ)) 0 ω ∧
        shifted D.X x t ω ∈ A} ∂positiveTimeLebesgue) := by
  sorry
