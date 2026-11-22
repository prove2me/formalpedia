-- Prove2me | Theorems.Thm_Kyprianou_Ch01_mckeanAffineSupportCoefficientTouch
-- name    : Kyprianou.Ch01.mckeanAffineSupportCoefficientTouch
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T20:49:58.70617+00:00
-- url     : https://prove2.me/theorems/bca26204-f8e7-4bd3-a59a-d6e5a4984c54
-- title:
--   McKean affine-exponential support has nonnegative coefficients and touches the value
-- statement:
--   Elementary coefficient and contact certificate for the Brownian McKean affine support: b=log(K phi/(1+phi)), u=min(y,b), A=K−(1+1/phi)exp(u)≥0, B=exp(u)/phi≥0; and V(y)=A+B exp(−phi(y-u)). Use exp(b)=K phi/(1+phi), exp(u)≤exp(b), and split y<b versus y≥b. In the continuation case A=0 and B=K−exp(b); in exercise case u=y and the affine sum simplifies to K−exp(y). This is a necessary certificate imported by the mission-connected global supporting majorant.
-- source:
--   Kyprianou (2006) Chapter 1 McKean perpetual put, coefficient positivity and smooth-fit contact.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
open MeasureTheory ProbabilityTheory Kyprianou.Ch01
set_option autoImplicit false

theorem Kyprianou.Ch01.mckeanAffineSupportCoefficientTouch
    (K phi y : ℝ) (hK : 0 < K) (hphi : 0 < phi) :
    let b : ℝ := Real.log (K * phi / (1 + phi))
    let u : ℝ := min y b
    let A : ℝ := K - (1 + 1 / phi) * Real.exp u
    let B : ℝ := Real.exp u / phi
    0 ≤ A ∧ 0 ≤ B ∧
      mckeanValue K b phi y =
        A + B * Real.exp (-phi * (y - u)) := by sorry
