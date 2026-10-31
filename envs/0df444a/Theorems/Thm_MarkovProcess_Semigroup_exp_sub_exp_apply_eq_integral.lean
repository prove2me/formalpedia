-- Prove2me | Theorems.Thm_MarkovProcess_Semigroup_exp_sub_exp_apply_eq_integral
-- name    : MarkovProcess.Semigroup.exp_sub_exp_apply_eq_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:24:14.847135+00:00
-- url     : https://prove2.me/theorems/54cf3fd8-c3e5-40ec-b7a4-3ebfe18c99a2
-- title:
--   MarkovProcess: exp_sub_exp_apply_eq_integral
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Semigroup_Duhamel_d67aa5ca
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Duhamel estimates for bounded generators

This file gives the variation identity and contraction bounds needed to compare
exponentials of commuting bounded generators.  The identity is oriented as
`exp (t B) - exp (t A)`, so its integrand acts on `(B - A) x` and the resulting
estimate is immediately applicable to Yosida approximants.
-/

open MeasureTheory NormedSpace Set

namespace MarkovProcess.Semigroup

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/- Head-class caches: the repeated closed instance searches in this file are all
rooted at the operator type `E →L[ℝ] E`; resolving each once here keeps the
normed-hierarchy walk on `E` from being replayed at every `•` and `exp`. -/




/- `NormedSpace.exp`'s continuity lemma is now stated for a `ℚ`-normed algebra (the field
argument was dropped); this restricts the existing `NormedAlgebra ℝ (E →L[ℝ] E)` instance
along `ℚ ↪ ℝ` so `exp_continuous`/`fun_prop` can find it on `E →L[ℝ] E`. -/








end MarkovProcess.Semigroup


open MarkovProcess
open MarkovProcess.Semigroup
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Duhamel estimates for bounded generators

This file gives the variation identity and contraction bounds needed to compare
exponentials of commuting bounded generators.  The identity is oriented as
`exp (t B) - exp (t A)`, so its integrand acts on `(B - A) x` and the resulting
estimate is immediately applicable to Yosida approximants.
-/

open MeasureTheory NormedSpace Set


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/- Head-class caches: the repeated closed instance searches in this file are all
rooted at the operator type `E →L[ℝ] E`; resolving each once here keeps the
normed-hierarchy walk on `E` from being replayed at every `•` and `exp`. -/




/- `NormedSpace.exp`'s continuity lemma is now stated for a `ℚ`-normed algebra (the field
argument was dropped); this restricts the existing `NormedAlgebra ℝ (E →L[ℝ] E)` instance
along `ℚ ↪ ℝ` so `exp_continuous`/`fun_prop` can find it on `E →L[ℝ] E`. -/


open MarkovProcess.Semigroup in

theorem MarkovProcess.Semigroup.exp_sub_exp_apply_eq_integral (A B : E →L[ℝ] E) (hAB : Commute A B)
    (t : ℝ) (x : E) :
    exp (t • B) x - exp (t • A) x =
      ∫ s in 0..t, exp ((t - s) • A) (exp (s • B) ((B - A) x)) := by sorry
