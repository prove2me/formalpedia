-- Prove2me | Theorems.Thm_Kyprianou_Ch05_potentialAllScalesFromLaplaceRatios
-- name    : Kyprianou.Ch05.potentialAllScalesFromLaplaceRatios
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T21:45:39.116349+00:00
-- url     : https://prove2.me/theorems/20694763-622e-4a25-bd5a-d0c3a179b9f9
-- title:
--   Potential cumulative limit at each positive scale
-- statement:
--   A regularly varying exact reciprocal Laplace transform gives the potential cumulative limit at every positive scale.
-- source:
--   Kyprianou (2006), Lemma 5.17.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem Kyprianou.Ch05.potentialAllScalesFromLaplaceRatios
    (U : Measure Real) (Phi : Real → Real) (rho : Real)
    (l l' : Filter Real) (hrho : 0 ≤ rho)
    (hs : U (Iio 0) = 0)
    (hpos : ∀ t : Real, 0 < t → 0 < Phi t)
    (hLap : ∀ t : Real, 0 < t → positiveLaplace U t = (ENNReal.ofReal (Phi t))⁻¹)
    (he : ∀ᶠ x in l, 0 < x)
    (hi : Tendsto (fun x : Real => x⁻¹) l l')
    (hRV : ∀ t : Real, 0 < t → Tendsto
      (fun z => Phi (t*z)/Phi z) l' (nhds (t^rho)))
    (a : Real) (ha : 0 < a)
    (hScale : Tendsto (fun x : Real => a*x) l l) :
    Tendsto (fun x => (U (Icc 0 (a*x))).toReal * Phi (1/x)) l
      (nhds (a^rho/Real.Gamma (1+rho))) := by sorry
