-- Prove2me | Theorems.Thm_Kyprianou_Ch01_passageLaplaceNormBoundNonnegativeDiscountPublic
-- name    : Kyprianou.Ch01.passageLaplaceNormBoundNonnegativeDiscountPublic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T09:21:42.453056+00:00
-- url     : https://prove2.me/theorems/88c0d49f-87a3-4bc4-9398-8adee702face
-- title:
--   Brownian passage support: bounded discounted payoff at finite or infinite first passage
-- statement:
--   For every possibly infinite first-passage time and nonnegative discount, the real-valued discounted payoff has norm at most one. In the infinite-passage case the payoff is zero. This is a uniform dominating bound used in discounted passage limits.
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.10(ii) and 1.7, dominated convergence step, printed page 306 and 303 respectively.

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.NNReal.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.passageLaplaceNormBoundNonnegativeDiscountPublic
    {Ω : Type*} (τ : Ω → WithTop ℝ≥0)
    (q : ℝ) (hq : 0 ≤ q) (ω : Ω) :
    ‖passageLaplace τ q ω‖ ≤ (1 : ℝ) := by sorry
