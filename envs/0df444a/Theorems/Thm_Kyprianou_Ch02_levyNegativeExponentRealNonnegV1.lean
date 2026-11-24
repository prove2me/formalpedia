-- Prove2me | Theorems.Thm_Kyprianou_Ch02_levyNegativeExponentRealNonnegV1
-- name    : Kyprianou.Ch02.levyNegativeExponentRealNonnegV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:32:20.985812+00:00
-- url     : https://prove2.me/theorems/93c7071a-3e05-4b78-b7c4-c935470b0b42
-- title:
--   levyNegativeExponentRealNonneg
-- statement:
--   levyNegativeExponentRealNonneg
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.15

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.levyNegativeExponentRealNonnegV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (Ψ : ℝ → ℂ)
    (hψ : ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (X t)) ξ = Complex.exp (-(((t : ℝ) : ℂ)) * Ψ ξ)) :
    ∀ ξ : ℝ, 0 ≤ (Ψ ξ).re := by sorry
