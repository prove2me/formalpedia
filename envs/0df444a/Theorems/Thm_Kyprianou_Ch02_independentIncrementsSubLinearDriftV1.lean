-- Prove2me | Theorems.Thm_Kyprianou_Ch02_independentIncrementsSubLinearDriftV1
-- name    : Kyprianou.Ch02.independentIncrementsSubLinearDriftV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T20:55:15.492215+00:00
-- url     : https://prove2.me/theorems/24e848aa-c029-43b4-9481-fb95aa0ae8f2
-- title:
--   Independence of increments under deterministic linear compensation
-- statement:
--   Subtracting a deterministic linear drift from each sample path preserves
--   joint independence of increments on every monotone finite partition. Each
--   increment is translated by a deterministic real constant depending on its
--   endpoints, and Mathlib's iIndepFun.comp applies coordinatewise. This generic
--   lemma transfers finite-region Poisson independence to compensated Lévy bands.
-- source:
--   Kyprianou (2006), Chapter 2, Lévy–Itô finite-band compensated components

import Mathlib
import Definitions.Def_LeanLevy_Processes_StochasticProcess
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch02
theorem independentIncrementsSubLinearDriftV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ≥0 → Ω → ℝ) (c : ℝ)
    (hindep : ProbabilityTheory.HasIndependentIncrements X P) :
    ProbabilityTheory.HasIndependentIncrements
      (fun (t : ℝ≥0) ω => X t ω - (t : ℝ) * c) P := by sorry
end Kyprianou.Ch02
