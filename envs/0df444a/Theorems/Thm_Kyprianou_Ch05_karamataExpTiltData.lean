-- Prove2me | Theorems.Thm_Kyprianou_Ch05_karamataExpTiltData
-- name    : Kyprianou.Ch05.karamataExpTiltData
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T21:48:25.204312+00:00
-- url     : https://prove2.me/theorems/c8892dfc-7fc7-5bd4-907d-453e852b67f7
-- title:
--   Exponential tilt has finite mass, unit support and real power moments
-- statement:
--   Exponential tilt has finite mass, unit support and real power moments
-- source:
--   Kyprianou (2006), Theorem 5.13, compact moment proof of the Tauberian direction.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem Kyprianou.Ch05.karamataExpTiltData
    (M : Measure Real) (hs : M (Iio 0) = 0)
    (hfin : ∀ t : Real, 0 < t → positiveLaplace M t ≠ ⊤) :
    let N := ((M.withDensity (fun z : Real => ENNReal.ofReal (Real.exp (-z)))).map
      (fun z : Real => Real.exp (-z)))
    N univ ≠ ⊤ ∧ (∀ᵐ z ∂N, z ∈ Icc (0 : Real) 1) ∧
      (∀ n : Nat, Integrable (fun z : Real => z^n) N) ∧
      (∀ n : Nat, (∫ z : Real, z^n ∂N) =
        (positiveLaplace M ((n : Real)+1)).toReal) := by sorry
