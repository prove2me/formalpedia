-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmicCenterIdeal_canonical_power_le
-- name    : OAI.PiExponent.FormalInterpolation.logarithmicCenterIdeal_canonical_power_le
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T22:40:24.629415+00:00
-- url     : https://prove2.me/theorems/dd83e683-fbbe-4b5a-80d2-f992ef0b89c4
-- title:
--   One-center canonical truncation power comparison
-- statement:
--   For one center, the canonical logarithmic ideal raised to power `n + m` is contained in the arbitrary-truncation ideal raised to power `n`, under the same positivity and cutoff hypotheses as the target. It isolates the weighted logarithmic-coordinate comparison and its dimension loss.

import Definitions.Def_OAI_PiExponent_LogarithmicCenterIdeals
import Mathlib.RingTheory.Ideal.Operations

open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.logarithmicCenterIdeal_canonical_power_le
    {m : Nat} (c : Fin m → Complex)
    (T : Fin m → Nat) (e : Fin (m + 1) → Nat)
    (he : ∀ i, 0 < e i)
    (hcut : ∀ i, e 0 ≤ T i * e i.succ) (n : Nat) :
    (logarithmicCenterIdeal c (fun _ => e 0) e) ^ (n + m) ≤
      (logarithmicCenterIdeal c T e) ^ n := by sorry
