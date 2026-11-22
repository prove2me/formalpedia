-- Prove2me | Theorems.Thm_Kyprianou_Ch01_mg1OverloadedZeroIdleAtomFromRoot
-- name    : Kyprianou.Ch01.mg1OverloadedZeroIdleAtomFromRoot
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T00:34:00.42689+00:00
-- url     : https://prove2.me/theorems/d3e4da4f-8cce-4d25-8739-c132ef6f690e
-- title:
--   M/G/1 overloaded total idle time has exact zero-atom mass
-- statement:
--   Exact atom at zero for genuine overloaded M/G/1 idle-time regulator started at w, with fixed positive Lundberg exponent theta. Probability of totalIdleTime=0 is 1-exp(-theta*w). The original compound-Poisson driver, claim positivity and finite mean, no additional stochastic assumptions.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.9 overload idle-time distribution; exact child of mg1OverloadedIdleLawFromRoot.

import Mathlib
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set
open scoped NNReal ENNReal
set_option autoImplicit false
universe u

theorem Kyprianou.Ch01.mg1OverloadedZeroIdleAtomFromRoot
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
        1 - Real.exp (-theta * w) := by
  sorry
