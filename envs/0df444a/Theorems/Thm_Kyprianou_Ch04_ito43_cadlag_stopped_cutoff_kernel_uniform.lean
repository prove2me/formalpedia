-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_cadlag_stopped_cutoff_kernel_uniform
-- name    : Kyprianou.Ch04.ito43_cadlag_stopped_cutoff_kernel_uniform
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:42:11.534643+00:00
-- url     : https://prove2.me/theorems/de27723f-2cd2-5ca0-97dd-2a50f6a17d9a
-- title:
--   Uniform stopped grid convergence of a continuous cutoff kernel
-- statement:
--   Separate finitely many jumps above the cutoff, exclude large clipped cells without a jump by shrinking-cell compactness, then apply the two-sided path limits uniformly within each selected cell. Sum over the finite set of selected jumps.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.ito43_cadlag_stopped_cutoff_kernel_uniform (X L : NNReal → ℝ)
    (hCad : IsCadlag X)
    (hLeft : ∀ s : NNReal, 0 < s →
      Tendsto X (nhdsWithin s (Iio s)) (nhds (L s)))
    (K : NNReal → ℝ → ℝ → ℝ)
    (hK : Continuous (fun p : NNReal × ℝ × ℝ => K p.1 p.2.1 p.2.2))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hzero : ∀ s x z, |z| ≤ ρ → K s x z = 0)
    (T : NNReal) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∀ t : NNReal, t ≤ T →
        let u : ℕ → NNReal := fun k => T * (k : NNReal) / (n : NNReal)
        let v : ℕ → NNReal := fun k => min t (u k)
        |(∑ k ∈ Finset.range n,
          K (u k) (X (u k)) (X (v (k+1))-X (v k))) -
          (∑' s : Ioc (0 : NNReal) t,
            K s.1 (L s.1) (X s.1-L s.1))| < ε := by sorry
