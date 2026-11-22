-- Prove2me | Theorems.Thm_Kyprianou_Ch01_mg1StationaryWorkload
-- name    : Kyprianou.Ch01.mg1StationaryWorkload
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:14:58.848343+00:00
-- url     : https://prove2.me/theorems/c5f7df1b-21e9-4a87-8861-7c9760903f33
-- title:
--   Theorem 1.12(i): stationary M/G/1 workload Pollaczek–Khintchine CDF
-- statement:
--   In the light-traffic regime λμ<1, the workload distribution from any nonnegative initial workload converges to the compound-geometric integrated-tail distribution of Theorem 1.12(i). Draft declaration, not a proof; remote elaboration and source type audit pending.
-- source:
--   Kyprianou (2006), Introductory Lectures on Fluctuations of Lévy Processes with Applications, Theorem 1.12(i), p. 21.

import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Mathlib
import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false
universe u

theorem Kyprianou.Ch01.mg1StationaryWorkload
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
    (hlight : (rate : ℝ) * mu < 1)
    (eta : Measure ℝ) [IsProbabilityMeasure eta]
    (hetaSupport : eta (Set.Iio (0 : ℝ)) = 0)
    (heta : ∀ x : ℝ, 0 ≤ x →
      (eta (Set.Iic x)).toReal = integratedTailCDF F mu x) :
    ∀ w : ℝ, 0 ≤ w → ∀ x : ℝ, 0 ≤ x →
      Tendsto (fun t : ℝ≥0 =>
        (P {ω | queueWorkload arrival claims w t ω ≤ x}).toReal)
        atTop (nhds (pkCDF eta ((rate : ℝ) * mu) x)) := by
  sorry
