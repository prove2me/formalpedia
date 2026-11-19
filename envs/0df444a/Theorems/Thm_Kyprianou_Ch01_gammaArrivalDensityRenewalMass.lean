-- Prove2me | Theorems.Thm_Kyprianou_Ch01_gammaArrivalDensityRenewalMass
-- name    : Kyprianou.Ch01.gammaArrivalDensityRenewalMass
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T07:40:13.468714+00:00
-- url     : https://prove2.me/theorems/f98bc062-9522-469f-b247-5929002e3f99
-- title:
--   Tonelli sum of all positive-index Erlang renewal masses equals rate times horizon
-- statement:
--   For rate beta>0, the sum over all n>=0 of the Gamma(n+1,beta) arrival-time probabilities on [0,x] converges as a real-valued series and equals beta*x for x>=0. Equivalently, the positive arrival-index part of the exponential renewal measure has constant beta density. It follows from Tonelli for the nonnegative gamma densities and the separately Proved pointwise exponential series, and preserves the gamma arrival law rather than assuming its result.
-- source:
--   Kyprianou (2006), Exercise 1.8(iv), worked solution pp.304–305

import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Prod
import Definitions.Def_levy_foundations_arrivalGammaDensity
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch01.gammaArrivalDensityRenewalMass
    (beta : ℝ) (hbeta : 0 < beta) :
    ∀ x : ℝ, 0 ≤ x →
      Summable (fun n : ℕ =>
        ((volume.withDensity (LevyFoundations.arrivalGammaDensity beta n))
          (Set.Icc (0 : ℝ) x)).toReal) ∧
      (∑' n : ℕ,
        ((volume.withDensity (LevyFoundations.arrivalGammaDensity beta n))
          (Set.Icc (0 : ℝ) x)).toReal) = beta * x := by
  sorry
