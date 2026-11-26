-- Prove2me | Theorems.Thm_Kyprianou_Ch05_potentialLimitFromLaplaceRatios
-- name    : Kyprianou.Ch05.potentialLimitFromLaplaceRatios
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T21:42:52.566838+00:00
-- url     : https://prove2.me/theorems/f057d122-ca75-4444-bece-a3943052c28b
-- title:
--   Exact reciprocal potential transform and regular variation imply normalised cumulative limits
-- statement:
--   Exact reciprocal potential transform and regular variation imply normalised cumulative limits
-- source:
--   Kyprianou (2006), Theorem 5.13 and Lemma 5.17. Laplace–Stieltjes Tauberian implication.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_MonotoneDensity
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem Kyprianou.Ch05.potentialLimitFromLaplaceRatios
    (U : Measure Real) (Phi : Real → Real) (rho : Real)
    (l l' : Filter Real) (hrho : 0 ≤ rho)
    (hs : U (Iio 0) = 0)
    (hpos : ∀ t : Real, 0 < t → 0 < Phi t)
    (hLap : ∀ t : Real, 0 < t → positiveLaplace U t = (ENNReal.ofReal (Phi t))⁻¹)
    (he : ∀ᶠ x in l, 0 < x)
    (hi : Tendsto (fun x : Real => x⁻¹) l l')
    (hRV : ∀ t : Real, 0 < t → Tendsto
      (fun z => Phi (t*z)/Phi z) l' (nhds (t^rho))) :
    Tendsto (fun x => (U (Icc 0 x)).toReal * Phi (1/x)) l
      (nhds (1/Real.Gamma (1+rho))) := by sorry
