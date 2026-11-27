-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_qv_time_path_step_error
-- name    : Kyprianou.Ch04.ito43_qv_time_path_step_error
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:39:38.450595+00:00
-- url     : https://prove2.me/theorems/a3647ada-8918-43c2-bc49-431a079324a4
-- title:
--   Continuous path time step approximation bound on the physical horizon
-- statement:
--   Transport the nonnegative time-coordinate approximation to real time and apply the accepted finite-step time integral bound.
-- source:
--   Kyprianou (2006), Theorem 4.3 proof auxiliary

import Mathlib
import Definitions.Def_LeanLevy_Processes_Cadlag
open MeasureTheory Filter ProbabilityTheory Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.ito43_qv_time_path_step_error
    {Ω : Type} [MeasurableSpace Ω] (X L : NNReal → Ω → ℝ) (w : Ω)
    (hc : IsCadlag (fun s => X s w))
    (hl : ∀ s : NNReal, 0 < s →
      Tendsto (fun r => X r w) (nhdsWithin s (Iio s)) (nhds (L s w)))
    (g : ℝ × ℝ → ℝ) (hg : ContinuousOn g (Ici (0:ℝ) ×ˢ (univ : Set ℝ)))
    (T t : NNReal) (ht : t ≤ T) (δ : ℝ) (hδ : 0 ≤ δ)
    (m : ℕ) (b : ℕ → NNReal) (c : ℕ → ℝ)
    (hW : ∀ s ≤ T, |g ((s:ℝ),X s w) -
      ∑ i ∈ Finset.range m, c i * (if b i ≤ s then (1:ℝ) else 0)| ≤ δ) :
    |(∫ s in Icc (0:ℝ) (t:ℝ), g (s,X s.toNNReal w) ∂volume) -
      ∑ i ∈ Finset.range m, c i *
        ((∫ s in Icc (0:ℝ) (t:ℝ), (1:ℝ) ∂volume) -
          ∫ s in Icc (0:ℝ) ((min t (b i):NNReal):ℝ), (1:ℝ) ∂volume)| ≤
      δ * (T:ℝ) := by sorry
