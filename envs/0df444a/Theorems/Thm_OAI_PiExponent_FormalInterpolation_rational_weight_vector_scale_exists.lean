-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_rational_weight_vector_scale_exists
-- name    : OAI.PiExponent.FormalInterpolation.rational_weight_vector_scale_exists
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-08T07:00:31.851499+00:00
-- url     : https://prove2.me/theorems/03fd0224-0a41-43b7-8e09-840fb4a83219
-- title:
--   A common integer scale for rational weights
-- statement:
--   For a finite list of positive real weights that are all rational, one can choose a positive rational scale that is a positive integer multiple of every weight. The remaining weights can also each be bounded by an integer multiple of the first weight.
-- source:
--   Auxiliary arithmetic lemma for Prove2Me theorem OAI.PiExponent.FormalInterpolation.weighted_representative_scale_exists (a4ac5f9f-d4eb-4911-b163-47b9569c9156); the rationality and positivity hypotheses are precisely the properties used to construct the scale and integer bounds.

import Mathlib.Data.Real.Basic

import Mathlib.Data.Real.Basic

theorem OAI.PiExponent.FormalInterpolation.rational_weight_vector_scale_exists
    {m : Nat} (w : Fin (m + 1) -> Real)
    (hpos : forall i : Fin (m + 1), 0 < w i)
    (hrat : forall i : Fin (m + 1), exists r : Rat, (r : Real) = w i) :
    exists R : Rat, exists T : Fin m -> Nat, exists e : Fin (m + 1) -> Nat,
      And (0 < R) (And (forall i : Fin (m + 1), 0 < e i)
        (And (forall i : Fin m, w i.succ <= (T i : Real) * w 0)
          (forall i : Fin (m + 1), (R : Real) = (e i : Real) * w i))) := by sorry
