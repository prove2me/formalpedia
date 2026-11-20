-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAboveOneWeightedGammaCanonicalForm
-- name    : Kyprianou.Ch01.stableAboveOneWeightedGammaCanonicalForm
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T22:06:03.648477+00:00
-- url     : https://prove2.me/theorems/16a96d57-8adf-420b-802e-06dd90e8e4fc
-- title:
--   All-frequency weighted Gamma stable canonical form for 1<alpha<2
-- statement:
--   For 1<alpha<2 and cpos+cneg>0, the two weighted fractional-power Fourier phases equal stable scale -Gamma(-alpha)cos(pi alpha/2)(cpos+cneg)|xi|^alpha times the canonical skew beta tan(pi alpha/2) signed-frequency factor. Split xi>0, xi<0, xi=0 and reuse the exact positive/negative case proofs.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.4.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Real Complex Set
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAboveOneWeightedGammaCanonicalForm
    (alpha cpos cneg xi : ℝ)
    (ha1 : 1 < alpha) (ha2 : alpha < 2)
    (hnonzero : 0 < cpos + cneg) :
    let E : ℝ → ℂ := (fun z : ℝ => if z = 0 then (0 : ℂ) else
  Complex.exp ((alpha : ℂ) *
    Complex.log (-(Complex.I * (z : ℂ)))));
    let sgn : ℝ := if 0 < xi then 1 else if xi < 0 then -1 else 0;
    -((Real.Gamma (-alpha) : ℝ) : ℂ) *
      ((cpos : ℂ) * E xi + (cneg : ℂ) * E (-xi)) =
      (((-Real.Gamma (-alpha) * Real.cos (Real.pi * alpha / 2) *
          (cpos + cneg)) * |xi| ^ alpha : ℝ) : ℂ) *
        (1 - Complex.I *
          (((((cpos - cneg) / (cpos + cneg)) *
            Real.tan (Real.pi * alpha / 2) * sgn : ℝ) : ℂ))) := by sorry
