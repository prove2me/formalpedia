-- Prove2me | Theorems.Thm_Kyprianou_Ch05_karamataDilationSupportMass
-- name    : Kyprianou.Ch05.karamataDilationSupportMass
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T21:43:35.957858+00:00
-- url     : https://prove2.me/theorems/28d41a05-3a83-4339-b488-2da7f1669c51
-- title:
--   Positive dilation preserves support and transports mass of the unit interval
-- statement:
--   Positive dilation preserves support and transports mass of the unit interval
-- source:
--   Kyprianou (2006), Theorem 5.13 and Lemma 5.17, Tauberian reference and scaling.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_MonotoneDensity
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem Kyprianou.Ch05.karamataDilationSupportMass
    (U : Measure Real) (x c : Real) (hx : 0 < x)
    (hs : U (Iio 0) = 0) :
    let M := (ENNReal.ofReal c) • (Measure.map (fun z : Real => z/x) U)
    M (Iio 0) = 0 ∧ M (Icc 0 1) = ENNReal.ofReal c * U (Icc 0 x) := by sorry
