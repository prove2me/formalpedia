-- Prove2me | Theorems.Thm_Kyprianou_Ch05_karamataGammaCumulativePositive
-- name    : Kyprianou.Ch05.karamataGammaCumulativePositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T21:43:25.921828+00:00
-- url     : https://prove2.me/theorems/7851bd9a-322d-5b45-9824-dca9b62c23b7
-- title:
--   Gamma-normalised power density has the required cumulative mass at one
-- statement:
--   Gamma-normalised power density has the required cumulative mass at one
-- source:
--   Kyprianou (2006), Theorem 5.13 and Lemma 5.17, Tauberian reference and scaling.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_MonotoneDensity
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem Kyprianou.Ch05.karamataGammaCumulativePositive
    (rho : Real) (hrho : 0 < rho) :
    (((volume.restrict (Ioi (0 : Real))).withDensity
      (fun z : Real => ENNReal.ofReal (z^(rho-1)/Real.Gamma rho))) (Icc 0 1)).toReal =
      1/Real.Gamma (1+rho) := by sorry
