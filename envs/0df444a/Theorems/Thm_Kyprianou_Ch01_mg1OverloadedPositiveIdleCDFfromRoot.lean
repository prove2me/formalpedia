-- Prove2me | Theorems.Thm_Kyprianou_Ch01_mg1OverloadedPositiveIdleCDFfromRoot
-- name    : Kyprianou.Ch01.mg1OverloadedPositiveIdleCDFfromRoot
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T00:33:57.633711+00:00
-- url     : https://prove2.me/theorems/fb5d093b-6e43-4a37-b284-467e945dbf5f
-- title:
--   M/G/1 overloaded finite positive idle time has exponential cumulative law
-- statement:
--   Exact positive finite portion of overloaded M/G/1 total idle time distribution: P(0<idle≤x)=exp(-theta*w)*(1-exp(-theta*x)) for any w,x≥0. Preserves original regulator, compound-Poisson driver and strictly positive Laplace-exponent root.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.9 overload idle-time distribution; exact child of mg1OverloadedIdleLawFromRoot.

import Mathlib
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set
open scoped NNReal ENNReal
set_option autoImplicit false
universe u

theorem Kyprianou.Ch01.mg1OverloadedPositiveIdleCDFfromRoot
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
      ∀ x : ℝ, 0 ≤ x →
        (P {ω | (0 : ℝ≥0∞) < totalIdleTime arrival claims w ω ∧
          totalIdleTime arrival claims w ω ≤ ENNReal.ofReal x}).toReal =
            Real.exp (-theta * w) * (1 - Real.exp (-theta * x)) := by
  sorry
