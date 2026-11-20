-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaOneCanonicalFromTripletPhase
-- name    : Kyprianou.Ch01.stableAlphaOneCanonicalFromTripletPhase
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T16:02:48.453117+00:00
-- url     : https://prove2.me/theorems/c4751e69-4f56-4265-89e4-7c58ecee8658
-- title:
--   Cauchy stable signed-triplet phase implies canonical index-one scale and skew form
-- statement:
--   Given the exact signed index-one Levy triplet phase with coefficients cpos+cneg and cpos-cneg, identify positive stable scale c=pi*(cpos+cneg)/2, skew beta=(cpos-cneg)/(cpos+cneg), and linear drift correction eta= -T.drift -(cpos-cneg)*k. The identity holds for all xi including zero.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.4 (alpha-one): Cauchy stable characteristic exponent phase algebra.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Real Set Kyprianou.Ch01
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaOneCanonicalFromTripletPhase
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (cpos cneg : ℝ) (hsum : 0 < cpos + cneg)
    (hphase : ∃ k : ℝ, ∀ xi : ℝ,
      -Kyprianou.Ch01.levyTripleExponent T xi =
        (((Real.pi * (cpos + cneg) * |xi| / 2 : ℝ) : ℂ) +
          Complex.I * ((((cpos - cneg) * xi * Real.log |xi| : ℝ) : ℂ)) -
          Complex.I * ((((T.drift + (cpos - cneg) * k) * xi : ℝ) : ℂ)))) :
    ∃ c beta eta : ℝ,
      0 < c ∧ beta = (cpos - cneg) / (cpos + cneg) ∧
      ∀ xi : ℝ,
        let sgn : ℝ := if 0 < xi then 1 else if xi < 0 then -1 else 0
        (-Kyprianou.Ch01.levyTripleExponent T xi =
          ((c * |xi| : ℝ) : ℂ) *
            (1 + Complex.I *
              (((beta * (2 / Real.pi) * sgn * Real.log |xi| : ℝ) : ℂ))) +
          Complex.I * (((eta * xi : ℝ) : ℂ))) := by sorry
