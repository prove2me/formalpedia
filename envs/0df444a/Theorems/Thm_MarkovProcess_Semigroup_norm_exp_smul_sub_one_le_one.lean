-- Prove2me | Theorems.Thm_MarkovProcess_Semigroup_norm_exp_smul_sub_one_le_one
-- name    : MarkovProcess.Semigroup.norm_exp_smul_sub_one_le_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:31:32.720979+00:00
-- url     : https://prove2.me/theorems/e643861b-543b-4c59-87e3-f8ac44e25c24
-- title:
--   MarkovProcess: norm_exp_smul_sub_one_le_one
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Semigroup_ExponentialBounds_642305eb
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Exponential

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Norm bounds for Banach-algebra exponentials

This file records elementary estimates for the exponential in a real Banach algebra.  The
contraction estimate is tailored to exponentials of bounded Yosida-type generators.
-/

namespace MarkovProcess.Semigroup

open NormedSpace

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

/- `NormedSpace.exp_add_of_commute`'s continuity lemma is now stated for a `ℚ`-normed algebra
(the field argument was dropped); this restricts the existing `NormedAlgebra ℝ A` instance
along `ℚ ↪ ℝ` so it can be found on `A`. -/












end MarkovProcess.Semigroup


open MarkovProcess
open MarkovProcess.Semigroup
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Norm bounds for Banach-algebra exponentials

This file records elementary estimates for the exponential in a real Banach algebra.  The
contraction estimate is tailored to exponentials of bounded Yosida-type generators.
-/


open NormedSpace

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

/- `NormedSpace.exp_add_of_commute`'s continuity lemma is now stated for a `ℚ`-normed algebra
(the field argument was dropped); this restricts the existing `NormedAlgebra ℝ A` instance
along `ℚ ↪ ℝ` so it can be found on `A`. -/








open MarkovProcess.Semigroup in

theorem MarkovProcess.Semigroup.norm_exp_smul_sub_one_le_one [CompleteSpace A] [NormOneClass A]
    {c : ℝ} (hc : 0 ≤ c) {Q : A} (hQ : ‖Q‖ ≤ 1) :
    ‖exp (c • (Q - 1))‖ ≤ 1 := by sorry
