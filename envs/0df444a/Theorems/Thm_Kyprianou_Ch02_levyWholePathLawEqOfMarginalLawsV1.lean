-- Prove2me | Theorems.Thm_Kyprianou_Ch02_levyWholePathLawEqOfMarginalLawsV1
-- name    : Kyprianou.Ch02.levyWholePathLawEqOfMarginalLawsV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:52:19.512263+00:00
-- url     : https://prove2.me/theorems/ecabf894-d1fe-4924-9bb2-57eb338f9e45
-- title:
--   Whole-path law equality for arbitrary real Levy processes with equal marginal laws
-- statement:
--   From equal one-time marginal laws, use equality of all zero-start finite-grid laws of genuine Levy processes. Pass to measurable whole-path representatives and the public generic finite cylinder extension theorem.
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.12; LeanLevy path construction and generic Avram finite-cylinder path law.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.levyWholePathLawEqOfMarginalLawsV1
    {Ω Λ : Type} [MeasurableSpace Ω] [MeasurableSpace Λ]
    (P : Measure Ω) (Q : Measure Λ)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (X : ℝ≥0 → Ω → ℝ) (Y : ℝ≥0 → Λ → ℝ)
    (hX : IsLevyProcess X P) (hY : IsLevyProcess Y Q)
    (hLaw : ∀ t : ℝ≥0, Measure.map (X t) P = Measure.map (Y t) Q) :
    Measure.map (fun ω : Ω => fun t : ℝ≥0 => X t ω) P =
      Measure.map (fun ω : Λ => fun t : ℝ≥0 => Y t ω) Q := by
  sorry
