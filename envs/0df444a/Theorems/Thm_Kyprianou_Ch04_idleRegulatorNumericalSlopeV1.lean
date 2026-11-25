-- Prove2me | Theorems.Thm_Kyprianou_Ch04_idleRegulatorNumericalSlopeV1
-- name    : Kyprianou.Ch04.idleRegulatorNumericalSlopeV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T00:25:09.270632+00:00
-- url     : https://prove2.me/theorems/e3aa214f-d7f1-466b-b501-95e6737f1a51
-- title:
--   Limit of the regulator slope from positive dyadic step bounds
-- statement:
--   At zero gap use the lower bound d-q and the upper bound d, then pass to the limit. At positive gap the upper bound vanishes eventually, forcing a zero limit.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.1; deterministic regulator calculus.

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.idleRegulatorNumericalSlopeV1
    (d gap k : Real) (hd : 0 < d) (hg : 0 ≤ gap)
    (step r q : Nat → Real) (hpos : ∀ n, 0 < step n)
    (hstep : Tendsto step atTop (𝓝 0))
    (hq : Tendsto q atTop (𝓝 0))
    (hr : Tendsto r atTop (𝓝 k))
    (hb : ∀ n, 0 ≤ r n ∧
      r n ≤ max 0 (-gap + d * step n) / step n)
    (hl : gap = 0 → ∀ n, d - q n ≤ r n) :
    k = if gap = 0 then d else 0 := by
  sorry
