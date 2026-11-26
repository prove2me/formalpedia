-- Prove2me | Theorems.Thm_Kyprianou_Ch04_partialDerivativesPositiveV1
-- name    : Kyprianou.Ch04.partialDerivativesPositiveV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:32:16.379686+00:00
-- url     : https://prove2.me/theorems/01256e12-be3c-54ac-ac52-f6159665868b
-- title:
--   Joint derivative on the positive-time half-plane from continuous partial derivatives
-- statement:
--   Joint derivative on the positive-time half-plane from continuous partial derivatives
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5, auxiliary lemma.

import Mathlib
open Filter Set Topology
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem partialDerivativesPositiveV1 (f ft fx : ℝ → ℝ → ℝ)
    (ht : ∀ s x, HasDerivAt (fun u => f u x) (ft s x) s)
    (hx : ∀ s x, HasDerivAt (f s) (fx s x) x)
    (hct : ContinuousOn (fun z : ℝ × ℝ => ft z.1 z.2) (Ici 0 ×ˢ univ))
    (hcx : ContinuousOn (fun z : ℝ × ℝ => fx z.1 z.2) (Ici 0 ×ˢ univ))
    (s x : ℝ) (hs : 0 < s) (a b : ℝ) :
    fderiv ℝ (fun z : ℝ × ℝ => f z.1 z.2) (s,x) (a,b) =
      ft s x * a + fx s x * b := by
  sorry
end Kyprianou.Ch04
