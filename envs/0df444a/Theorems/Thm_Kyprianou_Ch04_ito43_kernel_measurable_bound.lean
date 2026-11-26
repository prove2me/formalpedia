-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_kernel_measurable_bound
-- name    : Kyprianou.Ch04.ito43_kernel_measurable_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:38:13.657864+00:00
-- url     : https://prove2.me/theorems/7dcfc968-58bc-47a0-a1fc-d90bb039a92b
-- title:
--   Measurable compact envelope for continuous kernel along cadlag paths
-- statement:
--   Measurable compact envelope for continuous kernel along cadlag paths.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory Filter ProbabilityTheory Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.ito43_kernel_measurable_bound {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → ℝ)
    (hX : Measurable (fun z : NNReal × Omega => X z.1 z.2))
    (hCad : ∀ w, IsCadlag (fun t => X t w))
    (g : ℝ × ℝ → ℝ)
    (hg : ContinuousOn g (Ici (0 : ℝ) ×ˢ (univ : Set ℝ))) (T : NNReal) :
    ∃ M : Omega → ℝ, Measurable M ∧ (∀ w, 0 ≤ M w) ∧
      ∀ w s, s ∈ Icc (0 : ℝ) (T : ℝ) → ∀ r : NNReal, r ≤ T → |g (s,X r w)| ≤ M w := by sorry
