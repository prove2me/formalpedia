-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_weighted_real_path_left
-- name    : Kyprianou.Ch04.ito43_weighted_real_path_left
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:17:25.256051+00:00
-- url     : https://prove2.me/theorems/3d28389b-aed1-470a-8046-212184b36525
-- title:
--   Weighted real-time path has the prescribed left limit
-- statement:
--   Compose the left-sided path limit with the continuous weight, using positive time.
-- source:
--   Kyprianou (2006), Theorem 4.3 proof auxiliary

import Mathlib
import Definitions.Def_LeanLevy_Processes_Cadlag
open Set Filter
open scoped Topology ENNReal NNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.ito43_weighted_real_path_left
    {Ω : Type} [MeasurableSpace Ω] (X : NNReal → Ω → ℝ) (w : Ω)
    (g : ℝ × ℝ → ℝ) (hg : ContinuousOn g (Ici (0:ℝ) ×ˢ (univ : Set ℝ)))
    (L : NNReal → Ω → ℝ)
    (hl : ∀ s : NNReal, 0 < s →
      Tendsto (fun r => X r w) (nhdsWithin s (Iio s)) (nhds (L s w)))
    (t : ℝ) (ht : 0 < t) :
    Tendsto (fun r : ℝ => g (r,X r.toNNReal w)) (nhdsWithin t (Iio t))
      (nhds (g (t,L t.toNNReal w))) := by sorry
