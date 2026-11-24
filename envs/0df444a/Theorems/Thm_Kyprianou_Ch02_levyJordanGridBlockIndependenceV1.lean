-- Prove2me | Theorems.Thm_Kyprianou_Ch02_levyJordanGridBlockIndependenceV1
-- name    : Kyprianou.Ch02.levyJordanGridBlockIndependenceV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:38:48.970122+00:00
-- url     : https://prove2.me/theorems/8dc9640d-fa62-48f6-b6b4-f9e5e55a8fc0
-- title:
--   Jordan grid-sum pairs on consecutive intervals are mutually independent
-- statement:
--   Concatenate equal-grid subdivisions of all consecutive intervals in a monotone partition. The entire fine-grid increment family is independent. Reindex using the pair of block and cell indices, group each block by iIndepFun.iIndepFun_process₀, then apply measurable positive/negative sum maps blockwise.
-- source:
--   Kyprianou (2006), Exercise 2.8; common equal-grid approximation route.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.levyJordanGridBlockIndependenceV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P) :
    let G : ℕ → ℝ≥0 → ℝ≥0 → Ω → ℝ × ℝ := fun n a b ω =>
      let g (k : ℕ) := a + (b-a)*(k : ℝ≥0)/((n+1 : ℕ) : ℝ≥0)
      let d (k : ℕ) := X (g (k+1)) ω - X (g k) ω
      (∑ k : Fin (n+1), max (d k) 0, ∑ k : Fin (n+1), max (-d k) 0)
    ∀ (n m : ℕ) (t : Fin (m+1) → ℝ≥0), Monotone t →
      iIndepFun (fun i : Fin m => G n (t i.castSucc) (t i.succ)) P := by sorry
