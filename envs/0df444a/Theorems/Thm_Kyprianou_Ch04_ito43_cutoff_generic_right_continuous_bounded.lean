-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_cutoff_generic_right_continuous_bounded
-- name    : Kyprianou.Ch04.ito43_cutoff_generic_right_continuous_bounded
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T18:46:03.422681+00:00
-- url     : https://prove2.me/theorems/ea8bd8f8-0883-567a-a887-5b32dd699a4d
-- title:
--   Generic stopped cutoff kernel error is bounded and right continuous
-- statement:
--   For every compact horizon only finitely many retained actual jumps occur. Their cumulative sum is right continuous and locally bounded. Each grid cell depends on the stopping time through right-continuous clipped path evaluations, and finite sums preserve boundedness.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.ito43_cutoff_generic_right_continuous_bounded (X L : NNReal → ℝ)
    (hCad : IsCadlag X)
    (hLeft : ∀ s : NNReal, 0 < s →
      Tendsto X (nhdsWithin s (Iio s)) (nhds (L s)))
    (K : NNReal → ℝ → ℝ → ℝ)
    (hK : Continuous (fun p : NNReal × ℝ × ℝ => K p.1 p.2.1 p.2.2))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hzero : ∀ s x z, |z| ≤ ρ → K s x z = 0)
    (T : NNReal) :
    let E : ℕ → NNReal → ℝ := fun n t =>
      let u : ℕ → NNReal := fun k => T * (k : NNReal) / (n : NNReal)
      let v : ℕ → NNReal := fun k => min t (u k)
      (∑' s : Set.Ioc (0 : NNReal) t, K s.1 (L s.1) (X s.1-L s.1)) -
        (∑ k ∈ Finset.range n, K (u k) (X (u k))
          (X (v (k+1))-X (v k)))
    ∀ n, (∀ t, ContinuousWithinAt (fun s => |E n s|) (Set.Ici t) t) ∧
      BddAbove (Set.range (fun t : Set.Iic T => |E n t|)) := by sorry
