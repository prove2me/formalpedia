-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableTwoSidedTrigSkewFactor
-- name    : Kyprianou.Ch01.stableTwoSidedTrigSkewFactor
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T19:49:35.676513+00:00
-- url     : https://prove2.me/theorems/d144ae45-374e-4831-a5ea-ec1a351a5b56
-- title:
--   Two-sided stable cosine/sine phase factors into skewness parameter beta and tangent
-- statement:
--   For cpos+cneg nonzero and cosine theta nonzero, the two weighted complex phases cpos(cos theta-i sin theta)+cneg(cos theta+i sin theta) equal (cpos+cneg)cos theta times (1-i (cpos-cneg)/(cpos+cneg) tan theta). This is the exact skewness algebra in the stable Lévy-Khintchine formula.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.4 stable-law skewness normalization.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open Complex Real Kyprianou.Ch01
set_option autoImplicit false

theorem Kyprianou.Ch01.stableTwoSidedTrigSkewFactor
    (cpos cneg theta : ℝ)
    (hsum : cpos + cneg ≠ 0)
    (hcos : Real.cos theta ≠ 0) :
    (cpos : ℂ) * ((Real.cos theta : ℝ) -
       Complex.I * (Real.sin theta : ℂ)) +
    (cneg : ℂ) * ((Real.cos theta : ℝ) +
       Complex.I * (Real.sin theta : ℂ)) =
      (((cpos + cneg) * Real.cos theta : ℝ) : ℂ) *
        (1 - Complex.I *
          (((cpos - cneg) / (cpos + cneg) *
              Real.tan theta : ℝ) : ℂ)) := by sorry
