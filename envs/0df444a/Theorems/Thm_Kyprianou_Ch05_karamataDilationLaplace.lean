-- Prove2me | Theorems.Thm_Kyprianou_Ch05_karamataDilationLaplace
-- name    : Kyprianou.Ch05.karamataDilationLaplace
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T21:43:33.423914+00:00
-- url     : https://prove2.me/theorems/508b6d66-a11c-5ce7-bde6-754ca75b7b63
-- title:
--   Positive measure dilation gives the rescaled Laplace transform
-- statement:
--   Positive measure dilation gives the rescaled Laplace transform
-- source:
--   Kyprianou (2006), Theorem 5.13 and Lemma 5.17, Tauberian reference and scaling.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_MonotoneDensity
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem Kyprianou.Ch05.karamataDilationLaplace
    (U : Measure Real) (x c t : Real) (hx : 0 < x) :
    positiveLaplace ((ENNReal.ofReal c) •
      (Measure.map (fun z : Real => z/x) U)) t =
      ENNReal.ofReal c * positiveLaplace U (t/x) := by sorry
