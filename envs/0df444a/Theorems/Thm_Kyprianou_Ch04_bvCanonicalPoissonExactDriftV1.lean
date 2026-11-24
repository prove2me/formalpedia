-- Prove2me | Theorems.Thm_Kyprianou_Ch04_bvCanonicalPoissonExactDriftV1
-- name    : Kyprianou.Ch04.bvCanonicalPoissonExactDriftV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T23:06:59.053276+00:00
-- url     : https://prove2.me/theorems/fc756fbf-5fda-47f7-afd9-44f2f3fbd29b
-- title:
--   Canonical finite-variation Poisson model with the exact compensated drift
-- statement:
--   Strengthen the previously proved Chapter 2 canonical finite-variation model by retaining the actual drift witness from its accepted proof. Construct the canonical Poisson path using the same proof and its exact compensated drift.
-- source:
--   Kyprianou (2006), Chapter 2 Lemma 2.12 and Chapter 4 Theorem 4.2; explicit witness refinement of the proved canonical finite-variation model.

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_LeanLevy_Levy_CompensatedIntegral
open MeasureTheory ProbabilityTheory Complex Function
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.bvCanonicalPoissonExactDriftV1
    (a : ℝ) (levyMeasure : Measure ℝ)
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    (hfin : Integrable (fun x : ℝ => min (1 : ℝ) |x|) levyMeasure) :
    ∃ (Λ : Type) (mΛ : MeasurableSpace Λ),
      letI : MeasurableSpace Λ := mΛ
      ∃ (Q : Measure Λ) (Y : ℝ≥0 → Λ → ℝ),
        IsProbabilityMeasure Q ∧ IsLevyProcess Y Q ∧
        (∀ (t : ℝ≥0) (ξ : ℝ),
          charFun (Q.map (Y t)) ξ =
            Complex.exp ((((t : ℝ) : ℂ)) *
              (Complex.I * (((-a) * ξ : ℝ) : ℂ) +
                ∫ x, ProbabilityTheory.levyCompensatedIntegrand ξ x ∂levyMeasure))) ∧
        (∀ᵐ ω ∂Q, ∀ T : ℝ≥0,
          Summable (fun s : Set.Ioc (0 : ℝ≥0) T =>
            |Y (s : ℝ≥0) ω - leftLim (fun u : ℝ≥0 => Y u ω) (s : ℝ≥0)|) ∧
          Y T ω = (-a - ∫ x in Set.Ioo (-1 : ℝ) 1, x ∂levyMeasure) * (T : ℝ) +
            ∑' s : Set.Ioc (0 : ℝ≥0) T,
              (Y (s : ℝ≥0) ω - leftLim (fun u : ℝ≥0 => Y u ω) (s : ℝ≥0))) := by
  sorry
