-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_weighted_path_cutoff_limit
-- name    : Kyprianou.Ch04.ito43_weighted_path_cutoff_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:20:20.627401+00:00
-- url     : https://prove2.me/theorems/5dced150-ec7a-4e5c-ab2a-3c0c59469eae
-- title:
--   Weighted cutoff converges on every square-summable cadlag path
-- statement:
--   Use the proved weighted jump series summability, cutoff summable series limit, and conversion of real-time kernels to actual jump series.
-- source:
--   Kyprianou (2006), Theorem 4.3 proof auxiliary

import Mathlib
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_LeanLevy_Processes_Cadlag
open MeasureTheory Filter ProbabilityTheory Set
open scoped NNReal ENNReal Topology
open Kyprianou.Ch04
set_option autoImplicit false

theorem Kyprianou.Ch04.ito43_weighted_path_cutoff_limit
    {Ω : Type} [MeasurableSpace Ω]
    (X L : NNReal → Ω → ℝ) (w : Ω)
    (hc : IsCadlag (fun s => X s w))
    (hl : ∀ s : NNReal, 0 < s →
      Tendsto (fun r => X r w) (nhdsWithin s (Iio s)) (nhds (L s w)))
    (g : ℝ × ℝ → ℝ) (hg : ContinuousOn g (Ici (0:ℝ) ×ˢ (univ : Set ℝ)))
    (t : NNReal) (hs : Summable (fun s : Ioc (0:NNReal) t => (X s w-L s w)^2)) :
    Tendsto (fun m : ℕ =>
      ∫ z in Icc (0:ℝ) (t:ℝ) ×ˢ (univ : Set ℝ),
        g (z.1,L z.1.toNNReal w)*z.2^2/2 *
          min 1 (max 0 (|z.2| * ((m:ℝ)+1)-1))
          ∂(pathJumpMeasure X L w)) atTop
      (nhds (∫ z in Icc (0:ℝ) (t:ℝ) ×ˢ (univ : Set ℝ),
        g (z.1,L z.1.toNNReal w)*z.2^2/2 ∂(pathJumpMeasure X L w))) := by sorry
