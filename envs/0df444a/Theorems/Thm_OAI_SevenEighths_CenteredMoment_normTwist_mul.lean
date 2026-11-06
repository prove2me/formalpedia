-- Prove2me | Theorems.Thm_OAI_SevenEighths_CenteredMoment_normTwist_mul
-- name    : OAI.SevenEighths.CenteredMoment.normTwist_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:35:19.902738+00:00
-- url     : https://prove2.me/theorems/f1579bbe-a1ed-4f4a-ad1d-5aea90243463
-- title:
--   Centered Moment: norm Twist mul
-- statement:
--   The Centered Moment construction uses the norm Twist mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Moments/Basic.lean#L52-L55
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Moments/Basic.lean#L52-L55

import Mathlib.NumberTheory.MulChar.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Group.Commute.Units
import Definitions.Def_OAI_NumberTheory_DirichletL_Moments_Basic
set_option autoImplicit false
open OAI
open scoped BigOperators NNReal
open OAI.SevenEighths OAI.SevenEighths.CenteredMoment
noncomputable section
variable {M R : Type*} [CommMonoid M] [CommRing R]

theorem OAI.SevenEighths.CenteredMoment.normTwist_mul (N : M →* ℝ≥0) (t : ℝ) (a b : M) :
    normTwist N t (a * b) = normTwist N t a * normTwist N t b := by sorry
