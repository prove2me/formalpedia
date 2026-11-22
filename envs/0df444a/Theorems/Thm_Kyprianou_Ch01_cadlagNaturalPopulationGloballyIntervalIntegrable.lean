-- Prove2me | Theorems.Thm_Kyprianou_Ch01_cadlagNaturalPopulationGloballyIntervalIntegrable
-- name    : Kyprianou.Ch01.cadlagNaturalPopulationGloballyIntervalIntegrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T19:35:30.40336+00:00
-- url     : https://prove2.me/theorems/0bdc417b-dc69-46e3-8490-e473cd844c58
-- title:
--   Natural-valued càdlàg sample paths are interval-integrable on every finite real interval
-- statement:
--   Every natural-valued càdlàg NNReal-time path is Borel measurable and locally bounded, hence its real-time extension through Real.toNNReal has finite Bochner integral on each finite interval in ℝ. Use the existing Proved `Kyprianou.Ch01.cadlag_runningSup_bddAbove` on the continuous Nat-to-Real cast, which yields a uniform finite upper bound over each finite horizon, and nonnegativity supplies a lower bound. Obtain measurability of right-continuous paths by a countable-grid argument (or the proved generic rightContinuous_measurable_sections_joint_evaluation), and use bounded measurable integrability over a finite-volume interval. This is the source-faithful deterministic regularity needed for continuous Lamperti occupation paths, without finite offspring moments.
-- source:
--   Kyprianou (2006) Ch01 §1.3.4 Lamperti. Proved cadlag_runningSup_bddAbove UUID a92cc0c0-725a-4732-a803-82da495cb71b, Proved AvramDividend.Classical.rightContinuous_measurable_sections_joint_evaluation UUID 8aafec11-d8a5-443c-9386-270a0d5c8a04, and Proved branchingOccupationContinuousFromGlobalIntervalIntegrability UUID 15f351ae-d8d6-4230-94f9-3995abb4e7d9. This is a required child of branchingInverseOccupationMeasurablePathVersion UUID 986baeef-6b97-457a-9783-ef97e53a3f8b, connected through a SKETCH_ACCEPTED chain to original §1.3.4 root.

import Mathlib
import Definitions.Def_LeanLevy_Processes_Cadlag
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.cadlagNaturalPopulationGloballyIntervalIntegrable
    {Ω : Type*}
    (Y : ℝ≥0 → Ω → ℕ) (ω : Ω)
    (hCadlag : IsCadlag (fun t : ℝ≥0 => Y t ω)) :
    ∀ a b : ℝ,
      IntervalIntegrable
        (fun s : ℝ => (Y (Real.toNNReal s) ω : ℝ))
        volume a b := by
  sorry
