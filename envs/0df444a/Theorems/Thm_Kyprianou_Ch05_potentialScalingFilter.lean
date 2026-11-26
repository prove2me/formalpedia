-- Prove2me | Theorems.Thm_Kyprianou_Ch05_potentialScalingFilter
-- name    : Kyprianou.Ch05.potentialScalingFilter
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T20:38:32.671384+00:00
-- url     : https://prove2.me/theorems/2678bd1e-93c6-5aa8-bbcf-ca6549c6b292
-- title:
--   Karamata potential scaling at a general positive endpoint filter
-- statement:
--   Karamata potential scaling at a general positive endpoint filter
-- source:
--   Kyprianou (2006), Lemma 5.17 and Karamata's theorem, corrected reciprocal factor.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_MonotoneDensity
open MeasureTheory Filter ProbabilityTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem Kyprianou.Ch05.potentialScalingFilter
    (U : Measure Real) (Phi L : Real → Real) (rho : Real)
    (l : Filter Real) (hRho : 0 ≤ rho)
    (hpos : ∀ᶠ x in l, 0 < x)
    (hL : ∀ x : Real, 0 < x → 0 < L x)
    (hPhi : ∀ x : Real, 0 < x → Phi (1/x) = x^(-rho)/L x)
    (hCum : Tendsto (fun x : Real => (U (Icc 0 x)).toReal /
      (x^rho*L x/Real.Gamma (1+rho))) l (nhds 1))
    (a : Real) (ha : 0 < a)
    (hScale : Tendsto (fun x : Real => a*x) l l)
    (hSlow : Tendsto (fun x : Real => L (a*x)/L x) l (nhds 1)) :
    Tendsto (fun x : Real => (U (Icc 0 (a*x))).toReal*Phi (1/x)) l
      (nhds (a^rho/Real.Gamma (1+rho))) := by sorry
