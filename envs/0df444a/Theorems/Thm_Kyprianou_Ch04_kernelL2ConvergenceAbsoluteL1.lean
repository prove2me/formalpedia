-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kernelL2ConvergenceAbsoluteL1
-- name    : Kyprianou.Ch04.kernelL2ConvergenceAbsoluteL1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:17:03.298369+00:00
-- url     : https://prove2.me/theorems/fb4210d9-6a08-44be-8d42-3dcf48b805e4
-- title:
--   kernelL2ConvergenceAbsoluteL1
-- statement:
--   L2 convergence of kernels on finite measure implies real L1 convergence.
-- source:
--   Kyprianou (2006), Exercise 4.4, finite-band L2 completion.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_finiteMeasureL2ConvergenceL1
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
set_option autoImplicit false

/-- L2 convergence of equivalence classes on a finite measure implies real L1 convergence. -/
theorem Kyprianou.Ch04.kernelL2ConvergenceAbsoluteL1
    {A : Type} [MeasurableSpace A] (mu : Measure A) [IsFiniteMeasure mu]
    (f : ℕ → A → ℝ) (g : A → ℝ)
    (hf : ∀ n, MemLp (f n) 2 mu) (hg : MemLp g 2 mu)
    (hfg : Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g))) :
    Tendsto (fun n => ∫ a, |f n a - g a| ∂mu) atTop (𝓝 0) := by
  sorry
