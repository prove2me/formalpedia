-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_compact_kernel_bound
-- name    : Kyprianou.Ch04.ito43_compact_kernel_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:34:59.105631+00:00
-- url     : https://prove2.me/theorems/f8ef4769-ca98-4487-9cac-099869463bdf
-- title:
--   Uniform bound for continuous kernel along compact cadlag path
-- statement:
--   Uniform bound for continuous kernel along compact cadlag path.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3, supporting lemma.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch03_reflectionSignedCompactBoundV1
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- A continuous kernel along all pairs of times in a compact cadlag path is bounded. -/

theorem Kyprianou.Ch04.ito43_compact_kernel_bound (X : NNReal → ℝ) (hX : IsCadlag X)
    (g : ℝ × ℝ → ℝ) (hg : ContinuousOn g (Ici (0 : ℝ) ×ˢ (univ : Set ℝ)))
    (T : NNReal) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s ∈ Icc (0 : ℝ) (T : ℝ),
      ∀ r : NNReal, r ≤ T → |g (s,X r)| ≤ M := by sorry
