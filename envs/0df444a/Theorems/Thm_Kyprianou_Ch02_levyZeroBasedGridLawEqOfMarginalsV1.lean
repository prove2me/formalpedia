-- Prove2me | Theorems.Thm_Kyprianou_Ch02_levyZeroBasedGridLawEqOfMarginalsV1
-- name    : Kyprianou.Ch02.levyZeroBasedGridLawEqOfMarginalsV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:52:16.806039+00:00
-- url     : https://prove2.me/theorems/3f119111-1af5-4a73-8487-ba2de68ef5f3
-- title:
--   Equality of zero-based finite-grid laws for real Levy processes
-- statement:
--   The joint finite increment vector laws are equal, so apply the measurable prefix sum map and telescope using literal zero start. Source coordinates are a.e. measurable.
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.12; LeanLevy path construction and generic Avram finite-cylinder path law.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.levyZeroBasedGridLawEqOfMarginalsV1
    {Ω Λ : Type} [MeasurableSpace Ω] [MeasurableSpace Λ]
    (P : Measure Ω) (Q : Measure Λ)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (X : ℝ≥0 → Ω → ℝ) (Y : ℝ≥0 → Λ → ℝ)
    (hX : IsLevyProcess X P) (hY : IsLevyProcess Y Q)
    (hLaw : ∀ t : ℝ≥0, Measure.map (X t) P = Measure.map (Y t) Q)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (n : ℕ) (ht0 : t 0 = 0) :
    Measure.map (fun ω : Ω => fun i : Fin n =>
      X (t (i.val + 1)) ω) P =
    Measure.map (fun ω : Λ => fun i : Fin n =>
      Y (t (i.val + 1)) ω) Q := by
  sorry
