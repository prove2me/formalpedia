-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_mark_cutoff_error_sections
-- name    : Kyprianou.Ch04.ito43_mark_cutoff_error_sections
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T20:21:38.323844+00:00
-- url     : https://prove2.me/theorems/8a72c607-d07c-560c-9a74-67b2fa25acbb
-- title:
--   Fixed-time mark cutoff errors are almost surely measurable
-- statement:
--   The grid sum is measurable by the measurable path sections. At each fixed time the jump series equals the limit of the grid sum by the proved deterministic cutoff convergence; use almost sure metrisable limit measurability.
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

theorem Kyprianou.Ch04.ito43_mark_cutoff_error_sections {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X L : NNReal → Ω → ℝ) (hX : IsLevyProcess X P)
    (hL : ∀ᵐ w ∂P, ∀ t : NNReal, 0 < t → Tendsto (fun s => X s w) (nhdsWithin t (Iio t)) (nhds (L t w)))
    (r : ℝ → ℝ) (hr : Continuous r) (δ : ℝ) (hδ : 0 < δ)
    (hzero : ∀ z, |z| ≤ δ → r z = 0) (T : NNReal) :
    let E : ℕ → NNReal → Ω → ℝ := fun n t w =>
      let u : ℕ → NNReal := fun k => T*(k:NNReal)/(n:NNReal)
      let v : ℕ → NNReal := fun k => min t (u k)
      (∫ z in Icc (0:ℝ) (t:ℝ) ×ˢ (univ : Set ℝ), r z.2 ∂(pathJumpMeasure X L w)) -
        ∑ k ∈ Finset.range n, r (X (v (k+1)) w-X (v k) w)
    ∀ n t, AEMeasurable (E n t) P := by sorry
