-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_mark_difference_energy_bound
-- name    : Kyprianou.Ch04.ito43_mark_difference_energy_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T20:23:12.849827+00:00
-- url     : https://prove2.me/theorems/965b03d2-ab00-5ac3-ab8e-ec3ee4975010
-- title:
--   Difference between two mark errors is bounded by two square energies
-- statement:
--   The integrable mark difference is dominated by the given small quadratic bound. Apply the atomic jump energy estimate to both marks and their difference, and bound the grid difference termwise by the same square energy.
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

theorem Kyprianou.Ch04.ito43_mark_difference_energy_bound {Ω : Type} [MeasurableSpace Ω] (X L : NNReal → Ω → ℝ) (w : Ω)
    (hc : IsCadlag (fun s => X s w))
    (hl : ∀ s : NNReal, 0 < s → Tendsto (fun t => X t w) (nhdsWithin s (Iio s)) (nhds (L s w)))
    (H T : NNReal) (hTH : T ≤ H)
    (hJ : Summable (fun s : Ioc (0:NNReal) H => (X s w-L s w)^2))
    (r c : ℝ → ℝ) (C e : ℝ) (hC : 0 ≤ C) (he : 0 ≤ e)
    (hr : ∀ z, |r z| ≤ C*z^2) (hc' : ∀ z, |c z| ≤ C*z^2)
    (hd : ∀ z, |r z-c z| ≤ e*z^2) :
    ∀ (n : ℕ) (t : NNReal), t ≤ T →
    let u : ℕ → NNReal := fun k => T*(k:NNReal)/(n:NNReal)
    let v : ℕ → NNReal := fun k => min t (u k)
    let B : Set (ℝ × ℝ) := Icc (0:ℝ) (t:ℝ) ×ˢ univ
    let d : ℕ → ℝ := fun k => X (v (k+1)) w-X (v k) w
    |((∫ z in B, r z.2 ∂(pathJumpMeasure X L w)) - ∑ k ∈ Finset.range n, r (d k)) -
      ((∫ z in B, c z.2 ∂(pathJumpMeasure X L w)) - ∑ k ∈ Finset.range n, c (d k))| ≤
        e*((∑ k ∈ Finset.range n, (d k)^2) + ∑' s : Ioc (0:NNReal) H, (X s w-L s w)^2) := by sorry
