-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaOneScaleSkewSignIdentity
-- name    : Kyprianou.Ch01.stableAlphaOneScaleSkewSignIdentity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T15:49:37.22799+00:00
-- url     : https://prove2.me/theorems/7c56530e-f6ab-4f3d-82bc-724800a3c202
-- title:
--   Stable index-one scale/skewness sign-normalisation identity
-- statement:
--   For positive total Lévy intensity cpos+cneg, the canonical scale c=π(cpos+cneg)/2 and skew β=(cpos-cneg)/(cpos+cneg) obey c|xi| β (2/π) sgn(xi)=(cpos-cneg)xi for every xi including zero. This is the exact coefficient identity in Kyprianou stable index-one characteristic exponent.
-- source:
--   Kyprianou (2006) Chapter 1 Exercise 1.4, alpha-one stable law scale/skewness normalisation.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Real Set Kyprianou.Ch01
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaOneScaleSkewSignIdentity
    (cpos cneg xi : ℝ) (hsum : 0 < cpos + cneg) :
    let c : ℝ := Real.pi * (cpos + cneg) / 2
    let beta : ℝ := (cpos - cneg) / (cpos + cneg)
    let sgn : ℝ := if 0 < xi then 1 else if xi < 0 then -1 else 0
    c * |xi| * beta * (2 / Real.pi) * sgn = (cpos - cneg) * xi := by sorry
