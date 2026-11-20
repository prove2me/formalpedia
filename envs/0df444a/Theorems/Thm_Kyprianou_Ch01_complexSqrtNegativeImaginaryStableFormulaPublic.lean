-- Prove2me | Theorems.Thm_Kyprianou_Ch01_complexSqrtNegativeImaginaryStableFormulaPublic
-- name    : Kyprianou.Ch01.complexSqrtNegativeImaginaryStableFormulaPublic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T07:36:55.482819+00:00
-- url     : https://prove2.me/theorems/563415c7-cf87-4f84-b854-022ebfe03ef2
-- title:
--   Principal complex square root of negative imaginary frequency gives half-stable skew factor
-- statement:
--   For every real frequency xi, the principal complex square root of -2 i xi equals sqrt(abs xi) times (1 - i sign xi), with sign xi defined by the explicit three-way conditional (positive, negative, zero). This is the deterministic branch identity converting the first-passage characteristic function's square-root exponent to the canonical alpha=1/2, beta=+1 stable characteristic exponent.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.10(ii), one-sided stable half characteristic exponent.

import Mathlib.Analysis.RCLike.Sqrt
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic
open Complex
set_option autoImplicit false

theorem Kyprianou.Ch01.complexSqrtNegativeImaginaryStableFormulaPublic (ξ : ℝ) :
    Complex.sqrt ((-2 : ℂ) * Complex.I * (ξ : ℂ)) =
      ((Real.sqrt (|ξ|) : ℝ) : ℂ) *
        (1 - Complex.I *
          (((if 0 < ξ then (1 : ℝ)
              else if ξ < 0 then -1 else 0) : ℝ) : ℂ)) := by sorry
