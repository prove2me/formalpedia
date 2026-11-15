-- Prove2me | Theorems.Thm_Kyprianou_Ch01_mg1IdleOverloaded
-- name    : Kyprianou.Ch01.mg1IdleOverloaded
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T08:14:19.942668+00:00
-- url     : https://prove2.me/theorems/20e81a72-7a0e-46c0-8945-d3a20c302db8
-- title:
--   Theorem 1.11(i): M/G/1 idle-time atom and exponential density in overload
-- statement:
--   Specifies existence and maximality of the positive nonzero root θ*, atom at zero of mass 1−e^{-θ*w}, and continuous exponential component of mass e^{-θ*w}; extended idle time retains a possible infinite value. Draft declaration, not a proof; remote elaboration and source type audit pending.
-- source:
--   Kyprianou (2006), Introductory Lectures on Fluctuations of Lévy Processes with Applications, Theorem 1.11(i), pp. 20–21.

import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Mathlib
import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false
universe u

theorem Kyprianou.Ch01.mg1IdleOverloaded
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
    (hoverload : 1 < (rate : ℝ) * mu) :
    ∃ theta : ℝ,
      0 < theta ∧ queueLaplaceExponent rate F theta = 0 ∧
      (∀ u : ℝ, theta < u → queueLaplaceExponent rate F u ≠ 0) ∧
      ∀ w : ℝ, 0 ≤ w →
        (P {ω | totalIdleTime arrival claims w ω = 0}).toReal =
          1 - Real.exp (-theta * w) ∧
        ∀ x : ℝ, 0 ≤ x →
          (P {ω | (0 : ℝ≥0∞) < totalIdleTime arrival claims w ω ∧
            totalIdleTime arrival claims w ω ≤ ENNReal.ofReal x}).toReal =
              Real.exp (-theta * w) * (1 - Real.exp (-theta * x)) := by
  sorry
