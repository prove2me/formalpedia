-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmicDegreeBound_finset_sum_job_5f95a2db
-- name    : OAI.PiExponent.FormalInterpolation.logarithmicDegreeBound_finset_sum_job_5f95a2db
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T04:59:44.846506+00:00
-- url     : https://prove2.me/theorems/d5aa6d62-8dd9-4e4a-a5df-d80e52ec9a42
-- title:
--   Weighted support bounds are closed under finite sums
-- statement:
--   A finite sum of polynomials satisfying one weighted support bound also satisfies it, by induction on the finite set and closure under addition. This includes the empty sum, whose support is empty.

import Definitions.Def_OAI_PiExponent_LogarithmicWordContact

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.logarithmicDegreeBound_finset_sum_job_5f95a2db
    {m : Nat} (w : Fin (m + 1) → Rat) (H : Real)
    {ι : Type*} (s : Finset ι)
    (f : ι → MvPolynomial (Fin (m + 1)) Complex)
    (hf : ∀ j ∈ s, logarithmicDegreeBound w H (f j)) :
    logarithmicDegreeBound w H (∑ j ∈ s, f j) := by sorry
