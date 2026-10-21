-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_scaling_headroom_local_interval
-- name    : OAI.PiExponent.FormalInterpolation.scaling_headroom_local_interval
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T12:48:31.501041+00:00
-- url     : https://prove2.me/theorems/826783ca-0d65-40a9-a59b-57ac7646b9db
-- title:
--   A common real interval preserving strict scaling bounds
-- statement:
--   For the given finite family of strict bounds, there is a positive real interval immediately to the right of 1 on which every bound remains true. At 1, each bound follows from the parent’s hypotheses; continuity and finiteness give a shared interval.

import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.scaling_headroom_local_interval
    (m : Nat) (A B : Real) (c d : Fin m -> Real)
    (hA : A < 1) (hB : B < 1)
    (hcd : forall i, c i < d i) :
    exists ε : Real, 0 < ε ∧
      forall x : Real, 1 < x → x < 1 + ε →
        (x ^ (m + 1) * A < 1) ∧
        (x ^ m * B < 1) ∧
        (forall i, x * c i < d i) := by sorry
