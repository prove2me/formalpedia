-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_positive_exponents_have_common_multiple
-- name    : OAI.PiExponent.FormalInterpolation.finite_positive_exponents_have_common_multiple
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T19:42:37.261994+00:00
-- url     : https://prove2.me/theorems/f2b7aad7-eecf-4778-821c-ec46c021cb49
-- title:
--   A common multiple for finitely many positive exponents
-- statement:
--   Every finite family of positive natural numbers has a positive common multiple. Taking the finite product proves the claim; for an empty family the product is 1 and the divisibility conditions are vacuous.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.finite_positive_exponents_have_common_multiple {ι : Type} [Fintype ι] (s : ι → Nat) (hs : ∀ i, 0 < s i) : ∃ S : Nat, 0 < S ∧ ∀ i, s i ∣ S := by sorry
