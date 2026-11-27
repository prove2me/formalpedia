-- Prove2me | Theorems.Thm_Kyprianou_Ch05_karamataExpTiltSupport
-- name    : Kyprianou.Ch05.karamataExpTiltSupport
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T21:48:28.610659+00:00
-- url     : https://prove2.me/theorems/f6133d3c-bd90-5033-b638-d1a4524fd507
-- title:
--   Exponential image of a supported tilted measure is supported on the unit interval
-- statement:
--   Exponential image of a supported tilted measure is supported on the unit interval
-- source:
--   Kyprianou (2006), Theorem 5.13, compact moment proof of the Tauberian direction.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem Kyprianou.Ch05.karamataExpTiltSupport
    (M : Measure Real) (hs : M (Iio 0) = 0) :
    ∀ᵐ z ∂((M.withDensity (fun z : Real => ENNReal.ofReal (Real.exp (-z)))).map
      (fun z : Real => Real.exp (-z))), z ∈ Icc (0 : Real) 1 := by sorry
