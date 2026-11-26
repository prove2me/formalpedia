-- Prove2me | Theorems.Thm_MasulloRH_dyadic_exp_row_sound
-- name    : MasulloRH.dyadic_exp_row_sound
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T10:11:40.939891+00:00
-- url     : https://prove2.me/theorems/05710f5b-63cc-5fda-8c58-5197cdec0fd6
-- title:
--   Every generated dyadic exponential row is valid and encloses the real exponential
-- statement:
--   Given any rational \(t\), compute a row for the existing public exponential certificate format. Zero has the exact output \([1,1]\). For \(t\le-64\) the output is \([0,2^{-64}]\). Otherwise put \(p=\max(1,\lceil4|t|\rceil)\) and \(x=|t|/p\). Round the published order-nine Taylor lower and upper estimates outward to multiples of \(2^{-32}\). At positive arguments take the interval of their \(p\)-th powers. At negative arguments use inverses in reverse order. Round the final endpoints outward again. Every generated row has the original argument, satisfies the published validity predicate, has nonnegative lower endpoint, and encloses the real exponential.
-- source:
--   Developed for the central height-two certificate https://prove2.me/theorems/44743777-9b41-5194-84da-ff2782e96168 using the public row definitions https://prove2.me/definitions/55b584ef-23cf-4152-bb89-68f7cb944cd5 .

import Definitions.Def_MasulloRH_DyadicExpRows

open MasulloRH.HeightTwoScalar MasulloRH.DyadicExp
set_option autoImplicit false

theorem MasulloRH.dyadic_exp_row_sound (t : ℚ) :
    (row t).argument = t ∧ (row t).Valid ∧ 0 ≤ (row t).lower ∧
      ((row t).lower:ℝ) ≤ Real.exp (t:ℝ) ∧ Real.exp (t:ℝ) ≤ ((row t).upper:ℝ) := by sorry
