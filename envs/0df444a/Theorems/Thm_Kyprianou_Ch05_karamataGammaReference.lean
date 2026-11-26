-- Prove2me | Theorems.Thm_Kyprianou_Ch05_karamataGammaReference
-- name    : Kyprianou.Ch05.karamataGammaReference
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T21:42:43.418518+00:00
-- url     : https://prove2.me/theorems/3caa7528-845c-54aa-a683-3d1d012248df
-- title:
--   Reference power-law measure with gamma-normalised Laplace transform
-- statement:
--   Reference power-law measure with gamma-normalised Laplace transform
-- source:
--   Kyprianou (2006), Theorem 5.13 and Lemma 5.17. Laplace–Stieltjes Tauberian implication.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_MonotoneDensity
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem Kyprianou.Ch05.karamataGammaReference
    (rho : Real) (hrho : 0 ≤ rho) :
    ∃ R : Measure Real, R (Iio 0) = 0 ∧ R {1} = 0 ∧
      (R (Icc 0 1)).toReal = 1 / Real.Gamma (1+rho) ∧
      ∀ t : Real, 0 < t → positiveLaplace R t = ENNReal.ofReal (t^(-rho)) := by sorry
