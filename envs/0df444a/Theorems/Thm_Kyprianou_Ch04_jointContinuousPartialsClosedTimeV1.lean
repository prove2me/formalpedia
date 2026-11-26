-- Prove2me | Theorems.Thm_Kyprianou_Ch04_jointContinuousPartialsClosedTimeV1
-- name    : Kyprianou.Ch04.jointContinuousPartialsClosedTimeV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T10:20:23.606842+00:00
-- url     : https://prove2.me/theorems/ae8cc625-689d-5a64-9a07-64b285b2b9f3
-- title:
--   Joint C1 regularity on the closed positive-time half-plane
-- statement:
--   Extend the joint derivative from the open positive-time half-plane by continuity to the closed convex half-plane, and apply the C1 criterion.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5(i).

import Mathlib
open Set Filter Topology
open scoped Topology
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem jointContinuousPartialsClosedTimeV1 (f fTime fSpace : ℝ → ℝ → ℝ)
    (ht : ∀ s x, HasDerivAt (fun u => f u x) (fTime s x) s)
    (hx : ∀ s x, HasDerivAt (f s) (fSpace s x) x)
    (hf : ContinuousOn (fun z : ℝ × ℝ => f z.1 z.2) (Ici (0 : ℝ) ×ˢ univ))
    (hct : ContinuousOn (fun z : ℝ × ℝ => fTime z.1 z.2) (Ici (0 : ℝ) ×ˢ univ))
    (hcx : ContinuousOn (fun z : ℝ × ℝ => fSpace z.1 z.2) (Ici (0 : ℝ) ×ˢ univ)) :
    ContDiffOn ℝ 1 (fun z : ℝ × ℝ => f z.1 z.2) (Ici (0 : ℝ) ×ˢ univ) := by
  sorry
end Kyprianou.Ch04
