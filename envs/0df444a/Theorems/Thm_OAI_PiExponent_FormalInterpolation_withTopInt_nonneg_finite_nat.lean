-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_withTopInt_nonneg_finite_nat
-- name    : OAI.PiExponent.FormalInterpolation.withTopInt_nonneg_finite_nat
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T18:13:37.204697+00:00
-- url     : https://prove2.me/theorems/369c577c-1532-4615-8d5e-77ece4c3846f
-- title:
--   Finite nonnegative WithTop integers are natural values
-- statement:
--   A finite nonnegative value in `WithTop Int` is the embedding of a natural number; zero corresponds to the natural number zero.
-- source:
--   openai/math Approximation FibreNormalRigidity: nonconstant fibre coordinates imply quantitative contact bound.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.Algebra.Order.WithTop.Untop0

open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.withTopInt_nonneg_finite_nat
    (v : WithTop Int) (hne : v ≠ ⊤) (hnonneg : 0 ≤ v) :
    ∃ k : Nat, v = ((k : Int) : WithTop Int) := by sorry
