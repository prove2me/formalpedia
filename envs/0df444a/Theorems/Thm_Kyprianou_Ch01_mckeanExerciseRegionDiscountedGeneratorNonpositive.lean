-- Prove2me | Theorems.Thm_Kyprianou_Ch01_mckeanExerciseRegionDiscountedGeneratorNonpositive
-- name    : Kyprianou.Ch01.mckeanExerciseRegionDiscountedGeneratorNonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T16:53:23.495803+00:00
-- url     : https://prove2.me/theorems/1cc92d4a-d7cf-43eb-9d3b-22cade89b131
-- title:
--   Discounted Brownian generator of McKean exercise payoff is nonpositive below the optimal barrier
-- statement:
--   The perpetual American put exercise payoff V(y)=K-exp(y) satisfies (L-q)V≤0 on the exercise region y≤b, with L=gamma*d/dy+sigma²/2*d²/dy² and b=log(K phi/(1+phi)). The exponent phi obeys the discounted Brownian characteristic equation, and the inequality follows from monotonicity of exp and elementary algebra. This verifies the HJB superharmonic inequality on the exercise region; in the continuation region (L-q)V=0 by the previously proved harmonic root theorem. Both are necessary for the original right-natural optional-sampling proof.
-- source:
--   Kyprianou (2006) Chapter 1 Theorem 1.13, HJB verification for perpetual American put.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.mckeanExerciseRegionDiscountedGeneratorNonpositive
    (sigma gamma K q phi y : ℝ)
    (hsigma : 0 < sigma) (hK : 0 < K) (hq : 0 < q)
    (hphi : 0 < phi)
    (hroot : (sigma ^ 2 / 2) * phi ^ 2 - gamma * phi - q = 0)
    (hy : y ≤ Real.log (K * phi / (1 + phi))) :
    (q - gamma - sigma ^ 2 / 2) * Real.exp y - q * K ≤ 0 := by sorry
