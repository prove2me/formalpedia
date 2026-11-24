-- Prove2me | Theorems.Thm_Kyprianou_Ch02_levyJordanGridLaplacePowerV1
-- name    : Kyprianou.Ch02.levyJordanGridLaplacePowerV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T00:04:15.98282+00:00
-- url     : https://prove2.me/theorems/9993be6e-b651-488e-bbc0-926b09dda98b
-- title:
--   Joint Laplace expectation of positive and negative grid sums is a cell power
-- statement:
--   Rewrite the exponential of the two sums as a product and apply the generic equal-grid product expectation identity.
-- source:
--   Kyprianou (2006), Exercise 2.8: Laplace factorisation of positive and negative variation.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.levyJordanGridLaplacePowerV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (hX : ProbabilityTheory.IsLevyProcess X P)
    (t : ℝ≥0) (n : ℕ) (u v : ℝ) :
    let g (k : ℕ) := t*(k : ℝ≥0)/((n+1 : ℕ) : ℝ≥0)
    let d (k : ℕ) (ω : Ω) := X (g (k+1)) ω-X (g k) ω
    let Z := X (t/((n+1 : ℕ) : ℝ≥0))
    (∫ ω, Real.exp (-(u*(∑ i : Fin (n+1), max (d i.val ω) 0)+
      v*(∑ i : Fin (n+1), max (-d i.val ω) 0))) ∂P) =
      (∫ ω, Real.exp (-(u*max (Z ω) 0+v*max (-Z ω) 0)) ∂P)^(n+1) := by sorry
