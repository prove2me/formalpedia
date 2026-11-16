-- Prove2me | Theorems.Thm_Kyprianou_Ch01_mckeanValueSmoothFit
-- name    : Kyprianou.Ch01.mckeanValueSmoothFit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T07:48:49.05325+00:00
-- url     : https://prove2.me/theorems/e02e34a6-ddf2-4101-8eaf-fa1df8f35305
-- title:
--   Exercise 1.10: smooth fit of the McKean optimal put value at its barrier
-- statement:
--   At the McKean optimal exercise boundary b=log(K phi/(1+phi)), the piecewise put value function is differentiable, and its derivative equals the immediate exercise payoff derivative -exp(b).
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.10, smooth-fit conjunct of original mckeanBrownianPutOptimal theorem.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping

open Kyprianou.Ch01 MeasureTheory ProbabilityTheory Set
set_option autoImplicit false

theorem Kyprianou.Ch01.mckeanValueSmoothFit
    (K phi : ℝ) (hK : 0 < K) (hphi : 0 < phi) :
    let b := Real.log (K * phi / (1 + phi))
    HasDerivAt (mckeanValue K b phi) (-Real.exp b) b := by sorry
