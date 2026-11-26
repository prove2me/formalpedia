-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_cutoff_selected_before
-- name    : Kyprianou.Ch04.ito43_cutoff_selected_before
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:48:29.388649+00:00
-- url     : https://prove2.me/theorems/d64e819e-6165-52f7-a12b-ce6af726468e
-- title:
--   Selected cutoff cell vanishes before its atom
-- statement:
--   If clipping is before the left endpoint the increment is zero. Otherwise both endpoints lie strictly before the atom and approach its left limit uniformly, so the increment lies inside the zero region.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.ito43_cutoff_selected_before (X L : NNReal → ℝ)
    (hCad : IsCadlag X)
    (hLeft : ∀ s : NNReal, 0 < s →
      Tendsto X (nhdsWithin s (Iio s)) (nhds (L s)))
    (K : NNReal → ℝ → ℝ → ℝ)
    (hK : Continuous (fun p : NNReal × ℝ × ℝ => K p.1 p.2.1 p.2.2))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hzero : ∀ s x z, |z| ≤ ρ → K s x z = 0)
    (T : NNReal)
    (s : NNReal) (hs : 0 < s) (hsT : s ≤ T) (j : ℕ → ℕ)
    (hj : ∀ᶠ n : ℕ in atTop,
      j n < n ∧ T * (j n : NNReal) / (n : NNReal) < s ∧
      s ≤ T * ((j n+1 : ℕ) : NNReal) / (n : NNReal)) :
    let u : ℕ → ℕ → NNReal := fun n k => T * (k : NNReal) / (n : NNReal)
    let C : ℕ → NNReal → ℕ → ℝ := fun n t k =>
      K (u n k) (X (u n k))
        (X (min t (u n (k+1))) - X (min t (u n k)))
    let A : NNReal → NNReal → ℝ := fun t s =>
      if s ≤ t then K s (L s) (X s-L s) else 0
    ∀ᶠ n : ℕ in atTop, ∀ t : NNReal, t < s → C n t (j n) = 0 := by sorry
