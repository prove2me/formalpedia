-- Prove2me | Theorems.Thm_Kyprianou_Ch05_karamataExpTiltRecoverMass
-- name    : Kyprianou.Ch05.karamataExpTiltRecoverMass
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T21:48:31.142553+00:00
-- url     : https://prove2.me/theorems/f760aa28-0b73-4808-ac8c-acce9a80fb0e
-- title:
--   Bounded inverse weighting of the compact exponential image recovers the original unit-interval mass
-- statement:
--   Bounded inverse weighting of the compact exponential image recovers the original unit-interval mass
-- source:
--   Kyprianou (2006), Theorem 5.13, compact moment proof of the Tauberian direction.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem Kyprianou.Ch05.karamataExpTiltRecoverMass
    (M : Measure Real) (hs : M (Iio 0) = 0) :
    let N := ((M.withDensity (fun z : Real => ENNReal.ofReal (Real.exp (-z)))).map
      (fun z : Real => Real.exp (-z)))
    let c := Real.exp (-1)
    (N.withDensity (fun z : Real => ENNReal.ofReal ((max z c)⁻¹))) (Ici c) =
      M (Icc 0 1) ∧ (M {1} = 0 → N {c} = 0) := by sorry
