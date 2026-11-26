-- Prove2me | Theorems.Thm_Kyprianou_Ch04_physicalItoRemainderEnvelopeV1
-- name    : Kyprianou.Ch04.physicalItoRemainderEnvelopeV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:21:05.559659+00:00
-- url     : https://prove2.me/theorems/ce56d15b-7d75-5d42-a197-198e45f049bb
-- title:
--   Quadratic small-mark and linear large-mark remainder envelope
-- statement:
--   Quadratic small-mark and linear large-mark remainder envelope.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5(iii).

import Mathlib
open Filter Set Topology
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem physicalItoRemainderEnvelopeV1 (f fSpace fSpace2 : ℝ → ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hSpace : ∀ s x, fSpace s x = deriv (fun u : ℝ => f s u) x)
    (hSpace2 : ∀ s x, fSpace2 s x = deriv (fun u : ℝ => fSpace s u) x)
    (hSmooth : ∀ s, ContDiff ℝ 2 (fun x => f s x))
    (hBound : ∀ s x, 0 ≤ s → |f s x| ≤ K ∧ |fSpace s x| ≤ K ∧ |fSpace2 s x| ≤ K) :
    ∀ s x z, 0 ≤ s →
      |f s (x+z) - f s x - z*fSpace s x| ≤
        K * min 1 (z^2) + (if 1 ≤ |z| then K*(2+|z|) else 0) := by
  sorry
end Kyprianou.Ch04
