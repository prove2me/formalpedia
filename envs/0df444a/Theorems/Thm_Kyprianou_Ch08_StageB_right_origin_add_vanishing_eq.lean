-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_right_origin_add_vanishing_eq
-- name    : Kyprianou.Ch08.StageB.right_origin_add_vanishing_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T08:08:03.915181+00:00
-- url     : https://prove2.me/theorems/b546a461-5faa-4e8e-b604-804652169859
-- title:
--   Right-origin equality for a Volterra difference with vanishing convolution
-- statement:
--   If f and g have right limits equal to their values at zero, K tends to zero on the right, and f(x)=g(x)+qK(x) for all x>0, then f(0)=g(0). This generic elementary topological bridge transfers the genuine source scale resolvent identity and vanishing causal convolution to discount invariance of the q-scale origin value.
-- source:
--   Kyprianou (2006) Lemma 8.3 equation (8.24), source-origin analytic argument.

import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology

namespace Kyprianou.Ch08.StageB

theorem right_origin_add_vanishing_eq
    (f g K : ℝ → ℝ) (q : ℝ)
    (hf : Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds (f 0)))
    (hg : Filter.Tendsto g (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds (g 0)))
    (hK : Filter.Tendsto K (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds (0 : ℝ)))
    (heq : ∀ x : ℝ, 0 < x → f x = g x + q * K x) :
    f 0 = g 0 := by
  sorry

end Kyprianou.Ch08.StageB
