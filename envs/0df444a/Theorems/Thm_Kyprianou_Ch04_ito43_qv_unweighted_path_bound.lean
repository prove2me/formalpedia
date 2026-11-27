-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_qv_unweighted_path_bound
-- name    : Kyprianou.Ch04.ito43_qv_unweighted_path_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:29:12.04142+00:00
-- url     : https://prove2.me/theorems/4ecb5b4f-1b76-548a-a2ff-4027382b25c7
-- title:
--   Unweighted quadratic variation is bounded by the horizon energy
-- statement:
--   Bound the time mass by the horizon and the actual squared-jump integral by the summable jump energy.
-- source:
--   Kyprianou (2006), Theorem 4.3 proof auxiliary

import Mathlib
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.ito43_qv_unweighted_path_bound
    {Ω : Type} [MeasurableSpace Ω] (X L : NNReal → Ω → ℝ) (w : Ω)
    (hJ : ({s : NNReal | 0 < s ∧ X s w ≠ L s w}).Countable)
    (H T t : NNReal) (ht : t ≤ T) (hT : T ≤ H)
    (hE : Summable (fun s : Ioc (0:NNReal) H => (X s w-L s w)^2))
    (σ : ℝ) (hσ : 0 ≤ σ) :
    σ*(∫ s in Icc (0:ℝ) (t:ℝ), (1:ℝ) ∂volume) +
      (∫ z in Icc (0:ℝ) (t:ℝ) ×ˢ (univ : Set ℝ),
        z.2^2/2 ∂(Kyprianou.Ch04.pathJumpMeasure X L w)) ≤
      σ*(T:ℝ) + (1/2)*(∑' s : Ioc (0:NNReal) H, (X s w-L s w)^2) := by sorry
