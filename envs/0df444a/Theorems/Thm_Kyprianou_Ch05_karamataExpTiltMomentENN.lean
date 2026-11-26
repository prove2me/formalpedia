-- Prove2me | Theorems.Thm_Kyprianou_Ch05_karamataExpTiltMomentENN
-- name    : Kyprianou.Ch05.karamataExpTiltMomentENN
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T21:48:28.195059+00:00
-- url     : https://prove2.me/theorems/b62db0cd-3fae-5ac7-94c3-7d16c4a159b5
-- title:
--   Exponential tilt and compact image turn Laplace transforms into integer moments
-- statement:
--   Exponential tilt and compact image turn Laplace transforms into integer moments
-- source:
--   Kyprianou (2006), Theorem 5.13, compact moment proof of the Tauberian direction.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem Kyprianou.Ch05.karamataExpTiltMomentENN
    (M : Measure Real) (n : Nat) :
    (∫⁻ z : Real, (ENNReal.ofReal z)^n ∂((M.withDensity (fun z : Real => ENNReal.ofReal (Real.exp (-z)))).map
      (fun z : Real => Real.exp (-z)))) =
      positiveLaplace M ((n : Real)+1) := by sorry
