-- Prove2me | Theorems.Thm_Kyprianou_Ch02_levyWholePathLawEqOfCharFunV1
-- name    : Kyprianou.Ch02.levyWholePathLawEqOfCharFunV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:52:15.561833+00:00
-- url     : https://prove2.me/theorems/fb4f56b5-ffee-4168-9061-55cb3b479b61
-- title:
--   Whole-path law equality for arbitrary real Levy processes with equal marginal characteristic functions
-- statement:
--   Use uniqueness of characteristic functions, genuine independent stationary increments and measurable versions of both entire paths to prove equality of the product-space path laws. No spectral negativity or a priori path law assumption.
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.12; LeanLevy path construction and generic Avram finite-cylinder path law.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.levyWholePathLawEqOfCharFunV1
    {Ω Λ : Type} [MeasurableSpace Ω] [MeasurableSpace Λ]
    (P : Measure Ω) (Q : Measure Λ)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (X : ℝ≥0 → Ω → ℝ) (Y : ℝ≥0 → Λ → ℝ)
    (hX : IsLevyProcess X P) (hY : IsLevyProcess Y Q)
    (hchar : ∀ t : ℝ≥0, ∀ ξ : ℝ,
      charFun (P.map (X t)) ξ = charFun (Q.map (Y t)) ξ) :
    Measure.map (fun ω : Ω => fun t : ℝ≥0 => X t ω) P =
      Measure.map (fun ω : Λ => fun t : ℝ≥0 => Y t ω) Q := by
  sorry
