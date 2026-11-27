-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_qv_threshold_crossing_error
-- name    : Kyprianou.Ch04.ito43_qv_threshold_crossing_error
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T22:14:05.515831+00:00
-- url     : https://prove2.me/theorems/ce465e17-88cb-440e-8987-552dcdde8a50
-- title:
--   Quadratic stopped grid threshold crossing error vanishes uniformly
-- statement:
--   Subtract the stopped square sums at the time and its minimum with the threshold. The only discrepancy from the threshold-selected left endpoints is the cell crossing the threshold. Its squared-increment difference is bounded by the post-threshold oscillation times twice the bounded path range, which vanishes by right continuity.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04
open scoped Topology

open Set

theorem Kyprianou.Ch04.ito43_qv_threshold_crossing_error  {Omega : Type} [MeasurableSpace Omega]
    (X Xleft : NNReal → Omega → ℝ) (w : Omega)
    (hc : IsCadlag (fun t => X t w))
    (hl : ∀ t : NNReal, 0 < t →
      Tendsto (fun s => X s w) (nhdsWithin t (Set.Iio t)) (nhds (Xleft t w)))
    (σ : ℝ) (hσ : 0 ≤ σ)
    (g : ℝ × ℝ → ℝ)
    (hg : ContinuousOn g (Set.Ici (0 : ℝ) ×ˢ (Set.univ : Set ℝ)))
    (T : NNReal)
    (hs : Summable (fun s : Set.Ioc (0:NNReal) (T+1) => (X s w-Xleft s w)^2))
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) :
    let Q : ℕ → NNReal → ℝ := fun n t =>
      let u : ℕ → NNReal := fun k => T*(k:NNReal)/(n:NNReal)
      let v : ℕ → NNReal := fun k => min t (u k)
      ∑ k ∈ Finset.range n, (X (v (k+1)) w-X (v k) w)^2/2
    ∀ b : NNReal, ∀ e : ℝ, 0 < e → ∀ᶠ n in atTop, ∀ t ≤ T,
      let u : ℕ → NNReal := fun k => T*(k:NNReal)/(N n:NNReal)
      let v : ℕ → NNReal := fun k => min t (u k)
      |Q (N n) t-Q (N n) (min t b) -
        ∑ k ∈ Finset.range (N n), (if b ≤ u k then (1:ℝ) else 0) *
          (X (v (k+1)) w-X (v k) w)^2/2| < e := by sorry
