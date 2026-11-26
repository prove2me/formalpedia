-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_mark_cutoff_ucp
-- name    : Kyprianou.Ch04.ito43_mark_cutoff_ucp
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T20:21:47.776454+00:00
-- url     : https://prove2.me/theorems/731a43f4-7e2f-47a1-b31e-fbba5a995188
-- title:
--   Continuous mark functions vanishing near zero converge uniformly in probability
-- statement:
--   The physical mark integral equals its jump series. On the common cadlag event use deterministic cutoff convergence and right continuity and boundedness. The measurable time-section and dense supremum lemmas give the measurable uniform error envelope.
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

theorem Kyprianou.Ch04.ito43_mark_cutoff_ucp {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X L : NNReal → Ω → ℝ) (hX : IsLevyProcess X P)
    (hL : ∀ᵐ w ∂P, ∀ t : NNReal, 0 < t → Tendsto (fun s => X s w) (nhdsWithin t (Iio t)) (nhds (L t w)))
    (r : ℝ → ℝ) (hr : Continuous r) (δ : ℝ) (hδ : 0 < δ)
    (hzero : ∀ z, |z| ≤ δ → r z = 0) (T : NNReal) :
    let E : ℕ → NNReal → Ω → ℝ := fun n t w =>
      let u : ℕ → NNReal := fun k => T*(k:NNReal)/(n:NNReal)
      let v : ℕ → NNReal := fun k => min t (u k)
      (∫ z in Icc (0:ℝ) (t:ℝ) ×ˢ (univ : Set ℝ), r z.2 ∂(pathJumpMeasure X L w)) -
        ∑ k ∈ Finset.range n, r (X (v (k+1)) w-X (v k) w)
    ∀ e : ℝ, 0 < e → Tendsto (fun n => (P {w | ∃ t ≤ T, e ≤ |E n t w|}).toReal) atTop (nhds 0) := by sorry
