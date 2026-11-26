-- Prove2me | Theorems.Thm_Kyprianou_Ch05_karamataCumulativeFromLaplaceRatios
-- name    : Kyprianou.Ch05.karamataCumulativeFromLaplaceRatios
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T21:42:48.86474+00:00
-- url     : https://prove2.me/theorems/4b110226-cb5a-47c2-a346-947da1728ff9
-- title:
--   Karamata cumulative implication from normalised Laplace ratios at a general endpoint
-- statement:
--   Karamata cumulative implication from normalised Laplace ratios at a general endpoint
-- source:
--   Kyprianou (2006), Theorem 5.13 and Lemma 5.17. Laplace–Stieltjes Tauberian implication.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_MonotoneDensity
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem Kyprianou.Ch05.karamataCumulativeFromLaplaceRatios
    (U : Measure Real) (c : Real → Real) (rho : Real)
    (l : Filter Real) (hrho : 0 ≤ rho)
    (hs : U (Iio 0) = 0)
    (hfin : ∀ t : Real, 0 < t → positiveLaplace U t ≠ ⊤)
    (he : ∀ᶠ x in l, 0 < x ∧ 0 ≤ c x)
    (hconv : ∀ t : Real, 0 < t → Tendsto
      (fun x => c x * (positiveLaplace U (t/x)).toReal) l
      (nhds (t^(-rho)))) :
    Tendsto (fun x => c x * (U (Icc 0 x)).toReal) l
      (nhds (1/Real.Gamma (1+rho))) := by sorry
