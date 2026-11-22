-- Prove2me | Theorems.Thm_Kyprianou_Ch01_cadlagNaturalPopulationMeasurableAndCompactBounded
-- name    : Kyprianou.Ch01.cadlagNaturalPopulationMeasurableAndCompactBounded
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T19:46:04.703801+00:00
-- url     : https://prove2.me/theorems/3c7e68d1-e6ff-4db9-86c0-abfb6dae9e6a
-- title:
--   Càdlàg natural population paths are measurable and uniformly bounded over finite horizons
-- statement:
--   For any natural-valued càdlàg path Y(·,ω) indexed by NNReal, its real-valued time-extension via Real.toNNReal is globally Borel measurable, and its population cast to Real has a nonnegative finite upper bound on every compact nonnegative-time interval [0,T]. Derive the cast path's right continuity and left limits via continuity of the Nat-to-Real coercion; use the public Proved AvramDividend.Classical.rightContinuous_measurable_sections_joint_evaluation specialised to Unit for measurability, then compose with measurable_real_toNNReal. Derive compact boundedness by the public Proved Kyprianou.Ch01.cadlag_runningSup_bddAbove. This separates the only high-cost path-measurability and boundedness obligations from the finite-volume interval-integrability step, overcoming Prove2Me's whole-theorem complexity gate.
-- source:
--   Kyprianou (2006) Chapter 1 §1.3.4 Lamperti inverse clock. Existing Proved Kyprianou.Ch01.cadlag_runningSup_bddAbove UUID a92cc0c0-725a-4732-a803-82da495cb71b, AvramDividend.Classical.rightContinuous_measurable_sections_joint_evaluation UUID 8aafec11-d8a5-443c-9386-270a0d5c8a04. Direct rootward child of newly published Kyprianou.Ch01.cadlagNaturalPopulationGloballyIntervalIntegrable UUID 0bdc417b-dc69-46e3-8490-e473cd844c58, connected via accepted sketch 6b3c334b-10e5-429c-ae78-f3821c4de51a to original §1.3.4 root.

import Mathlib
import Definitions.Def_LeanLevy_Processes_Cadlag
import Definitions.Def_Kyprianou_Ch01_ForwardLampertiPaths
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.cadlagNaturalPopulationMeasurableAndCompactBounded
    {Ω : Type*}
    (Y : ℝ≥0 → Ω → ℕ) (ω : Ω)
    (hCadlag : IsCadlag (fun t : ℝ≥0 => Y t ω)) :
    Measurable (fun s : ℝ => (Y (Real.toNNReal s) ω : ℝ)) ∧
    ∀ T : ℝ≥0, ∃ M : ℝ, 0 ≤ M ∧
      ∀ s : ℝ≥0, s ≤ T → (Y s ω : ℝ) ≤ M := by
  sorry
