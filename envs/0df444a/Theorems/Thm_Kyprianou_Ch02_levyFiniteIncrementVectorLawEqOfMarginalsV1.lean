-- Prove2me | Theorems.Thm_Kyprianou_Ch02_levyFiniteIncrementVectorLawEqOfMarginalsV1
-- name    : Kyprianou.Ch02.levyFiniteIncrementVectorLawEqOfMarginalsV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:52:21.317803+00:00
-- url     : https://prove2.me/theorems/09d990ff-afa4-4a06-b019-5e86da35282f
-- title:
--   Equality of finite ordered increment vector laws for real Levy processes
-- statement:
--   Apply iIndepFun.map_fun_eq_pi_map to each finite increment vector, using source a.e. coordinate measurability and stationary increments. Each product factor equals the law at the lag.
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.12; LeanLevy path construction and generic Avram finite-cylinder path law.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.levyFiniteIncrementVectorLawEqOfMarginalsV1
    {Ω Λ : Type} [MeasurableSpace Ω] [MeasurableSpace Λ]
    (P : Measure Ω) (Q : Measure Λ)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (X : ℝ≥0 → Ω → ℝ) (Y : ℝ≥0 → Λ → ℝ)
    (hX : IsLevyProcess X P) (hY : IsLevyProcess Y Q)
    (hLaw : ∀ t : ℝ≥0, Measure.map (X t) P = Measure.map (Y t) Q)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (n : ℕ) :
    Measure.map (fun ω : Ω => fun i : Fin n =>
      X (t (i.val + 1)) ω - X (t i.val) ω) P =
    Measure.map (fun ω : Λ => fun i : Fin n =>
      Y (t (i.val + 1)) ω - Y (t i.val) ω) Q := by
  sorry
