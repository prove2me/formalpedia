-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaOneTwoSidedPhaseAlgebra
-- name    : Kyprianou.Ch01.stableAlphaOneTwoSidedPhaseAlgebra
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T15:47:38.795175+00:00
-- url     : https://prove2.me/theorems/1b75cafd-f0b5-4ed0-8c9b-31ca21976a30
-- title:
--   Two-sided alpha-one logarithmic stable phase combines exactly into scale and skewness
-- statement:
--   The proven positive and negative Cauchy-stable kernel phases, with coefficients cpos and cneg, combine into a real term proportional to cpos+cneg, a logarithmic imaginary term proportional to cpos-cneg, and the corresponding linear phase correction. Pure algebra, no analytic assumptions.
-- source:
--   Kyprianou (2006) Chapter 1 Exercise 1.4 alpha=1; decomposition of two-sided positive and negative Levy kernel phases.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Real Set Kyprianou.Ch01
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaOneTwoSidedPhaseAlgebra
    (cpos cneg k xi : ℝ) :
    (cpos : ℂ) *
          ((((Real.pi * |xi| / 2 : ℝ) : ℂ) +
            Complex.I * (((xi * Real.log |xi| : ℝ) : ℂ)) -
            Complex.I * (((k * xi : ℝ) : ℂ)))) +
        (cneg : ℂ) *
          ((((Real.pi * |xi| / 2 : ℝ) : ℂ) -
            Complex.I * (((xi * Real.log |xi| : ℝ) : ℂ)) +
            Complex.I * (((k * xi : ℝ) : ℂ)))) = (((Real.pi * (cpos + cneg) * |xi| / 2 : ℝ) : ℂ) +
        Complex.I * (((((cpos - cneg) * xi * Real.log |xi| : ℝ)) : ℂ)) -
        Complex.I * (((((cpos - cneg) * k * xi : ℝ)) : ℂ))) := by sorry
