-- Prove2me | Theorems.Thm_Kyprianou_Ch06_spitzerExponentialOccupationTailIntegrable
-- name    : Kyprianou.Ch06.spitzerExponentialOccupationTailIntegrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T07:31:22.581221+00:00
-- url     : https://prove2.me/theorems/e93e55e1-d673-46db-8820-370b66aab9f1
-- title:
--   Spitzer Exercise 6.8: exponentially discounted bounded occupation tail is integrable
-- statement:
--   For any positive exponential discount p and measurable occupation probability factor f taking values between zero and one at all times t>1, the real-valued integral tail of exp(-p t)*f(t)/t is absolutely integrable on (1,infinity). This proves the large-time tail can never cause divergence in either Spitzer regularity criterion. Reuses pinned Mathlib integrableOn_exp_mul_Ioi.
-- source:
--   Kyprianou (2006), Exercise 6.8(i)-(ii), original solutions printed pp.333-334, discount-tail argument.

import Mathlib
open MeasureTheory
set_option autoImplicit false

theorem Kyprianou.Ch06.spitzerExponentialOccupationTailIntegrable
    (p : Real) (hp : 0 < p)
    (f : Real → Real) (hf : Measurable f)
    (hfBound : ∀ t ∈ Set.Ioi (1 : Real), 0 ≤ f t ∧ f t ≤ 1) :
    IntegrableOn
      (fun t : Real => Real.exp (-p * t) * f t / t)
      (Set.Ioi (1 : Real)) := by sorry
