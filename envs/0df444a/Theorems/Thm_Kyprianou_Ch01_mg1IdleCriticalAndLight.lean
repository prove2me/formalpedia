-- Prove2me | Theorems.Thm_Kyprianou_Ch01_mg1IdleCriticalAndLight
-- name    : Kyprianou.Ch01.mg1IdleCriticalAndLight
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:14:39.307287+00:00
-- url     : https://prove2.me/theorems/a496e411-0ea8-46f0-aa7a-bcc3747a5c1d
-- title:
--   Theorem 1.11(ii): infinite idle time for critical and light M/G/1 traffic
-- statement:
--   Total Lebesgue idle time is infinite almost surely whenever traffic intensity λμ≤1, including the equality case. Draft declaration, not a proof; remote elaboration and source type audit pending.
-- source:
--   Kyprianou (2006), Introductory Lectures on Fluctuations of Lévy Processes with Applications, Theorem 1.11(ii), p. 21.

import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Mathlib
import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false
universe u

theorem Kyprianou.Ch01.mg1IdleCriticalAndLight
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
    (hload : (rate : ℝ) * mu ≤ 1) :
    ∀ w : ℝ, 0 ≤ w →
      (P {ω | totalIdleTime arrival claims w ω = ⊤}).toReal = 1 := by
  sorry
