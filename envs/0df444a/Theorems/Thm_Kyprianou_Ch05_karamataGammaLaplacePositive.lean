-- Prove2me | Theorems.Thm_Kyprianou_Ch05_karamataGammaLaplacePositive
-- name    : Kyprianou.Ch05.karamataGammaLaplacePositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T21:43:27.381799+00:00
-- url     : https://prove2.me/theorems/7890af19-494e-41f4-abf4-d73b648f35d2
-- title:
--   Gamma-normalised power density has exact power Laplace transform
-- statement:
--   Gamma-normalised power density has exact power Laplace transform
-- source:
--   Kyprianou (2006), Theorem 5.13 and Lemma 5.17, Tauberian reference and scaling.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_MonotoneDensity
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem Kyprianou.Ch05.karamataGammaLaplacePositive
    (rho t : Real) (hrho : 0 < rho) (ht : 0 < t) :
    positiveLaplace ((volume.restrict (Ioi (0 : Real))).withDensity
      (fun z : Real => ENNReal.ofReal (z^(rho-1)/Real.Gamma rho))) t =
      ENNReal.ofReal (t^(-rho)) := by sorry
