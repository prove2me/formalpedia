-- Prove2me | Theorems.Thm_Kyprianou_Ch01_mg1OverloadedIdleLawFromRoot
-- name    : Kyprianou.Ch01.mg1OverloadedIdleLawFromRoot
-- status  : Open
-- author  : @WillR
-- created : 2026-11-18T23:20:51.364559+00:00
-- url     : https://prove2.me/theorems/356146a1-b67f-4973-8d2c-a8bf3d4bacea
-- title:
--   Supercritical M/G/1 idle-time zero atom and finite positive law for a Cramér root
-- statement:
--   For a genuine compound-Poisson arrival and claim driver in the overloaded M/G/1 regime, if theta is a strictly positive root of the original queue Laplace exponent, then total idle time has the source-exact atom of mass 1-exp(-theta w) at zero and the positive finite distribution exp(-theta w)*(1-exp(-theta x)). This isolates the substantive queueing path law from the separately proved existence and uniqueness of theta, preserving all original data.
-- source:
--   Kyprianou (2006) Chapter 1 Exercise 1.9 overloaded total idle-time law; original source-exact child.

import Mathlib
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set
open scoped NNReal ENNReal
set_option autoImplicit false
universe u

theorem Kyprianou.Ch01.mg1OverloadedIdleLawFromRoot
    {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (arrival claims : ℕ → Ω → ℝ) (rate : ℝ≥0)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hd : IsCompoundPoissonDriver arrival claims rate F P)
    (hrate : 0 < rate)
    (mu : ℝ) (hmu : 0 < mu)
    (hclaimpos : F (Set.Iic (0 : ℝ)) = 0)
    (hclaimint : Integrable (fun x : ℝ => x) F)
    (hmean : (∫ x, x ∂F) = mu)
    (theta : ℝ) (htheta : 0 < theta)
    (hroot : queueLaplaceExponent rate F theta = 0) :
    ∀ w : ℝ, 0 ≤ w →
      (P {ω | totalIdleTime arrival claims w ω = 0}).toReal =
        1 - Real.exp (-theta * w) ∧
      ∀ x : ℝ, 0 ≤ x →
        (P {ω | (0 : ℝ≥0∞) < totalIdleTime arrival claims w ω ∧
          totalIdleTime arrival claims w ω ≤ ENNReal.ofReal x}).toReal =
            Real.exp (-theta * w) * (1 - Real.exp (-theta * x)) := by
  sorry
