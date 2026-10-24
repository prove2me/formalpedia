-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_unitSimplexVolume_factorial_aux_step
-- name    : OAI.PiExponent.DeterminantContradiction.unitSimplexVolume_factorial_aux_step
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T14:32:41.784451+00:00
-- url     : https://prove2.me/theorems/cd6ec2a5-065f-4c8b-91ed-82f050e487bc
-- title:
--   Successor step for unit simplex volume
-- statement:
--   Assuming the closed-form volume in dimension n, prove it in dimension n+1. Slice by the last coordinate; each fiber is a scaled copy of the n-dimensional simplex, and Fubini plus the scaling law reduces the volume to the integral of (1 − t)^n on [0,1]. Evaluating that integral supplies the successor factorial factor. The statement preserves the closed simplex boundary and has no positivity restriction on n.

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

theorem OAI.PiExponent.DeterminantContradiction.unitSimplexVolume_factorial_aux_step (n : Nat)
    (h : MeasureTheory.volume
      {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧
        (Finset.univ.sum fun i : Fin n => x i) ≤ 1} =
      ENNReal.ofReal (1 / (Nat.factorial n : Real))) :
    MeasureTheory.volume
      {x : Fin (n + 1) → Real | (∀ i, 0 ≤ x i) ∧
        (Finset.univ.sum fun i : Fin (n + 1) => x i) ≤ 1} =
      ENNReal.ofReal (1 / (Nat.factorial (n + 1) : Real)) := by sorry
