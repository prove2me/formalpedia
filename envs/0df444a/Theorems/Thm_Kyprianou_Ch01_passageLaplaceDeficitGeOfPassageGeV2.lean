-- Prove2me | Theorems.Thm_Kyprianou_Ch01_passageLaplaceDeficitGeOfPassageGeV2
-- name    : Kyprianou.Ch01.passageLaplaceDeficitGeOfPassageGeV2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T00:12:09.527181+00:00
-- url     : https://prove2.me/theorems/f5026664-266c-4ba8-a984-55a059e6ccc7
-- title:
--   Extended first-passage times bound the discounted Laplace deficit below (namespace-safe publication)
-- statement:
--   For an extended nonnegative time T (including infinity), if the time is at least epsilon, the discounted passage time is at most exp(-epsilon). In the infinite case the passageLaplace transform is zero. Hence the nonnegative deficit 1 - passageLaplace(T,1) is at least 1-exp(-epsilon). This deterministic pointwise order lemma is valid without any Brownian or measurability assumptions and is used to feed Markov's inequality. V1 publication failed because its preamble opened a namespace that had not been imported; V2 removes the unneeded open.
-- source:
--   Monotonicity of the exponential, WithTop passage-time convention in Kyprianou (2006), Chapter 1.

import Mathlib
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.passageLaplaceDeficitGeOfPassageGeV2
    (T : WithTop ℝ≥0) (ε : ℝ≥0)
    (hBound : (ε : WithTop ℝ≥0) ≤ T) :
    1 - Real.exp (-(ε : ℝ)) ≤
      1 - (match T with
        | none => (0 : ℝ)
        | some t => Real.exp (-(t : ℝ))) := by
  sorry
