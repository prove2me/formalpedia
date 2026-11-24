-- Prove2me | Theorems.Thm_Kyprianou_Ch02_subordinationIncrementTestMixtureV1
-- name    : Kyprianou.Ch02.subordinationIncrementTestMixtureV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T23:59:29.795277+00:00
-- url     : https://prove2.me/theorems/16f08334-50c9-4988-b393-4be68fb4f9c6
-- title:
--   Independent clock single increment test mixture
-- statement:
--   Apply the independent random-time vector disintegration at the two times. Almost-sure monotonicity of the clock and stationarity of the deterministic increments turn the inner expectation into a lag kernel.
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.15.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Complex Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.subordinationIncrementTestMixtureV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (τ : ℝ≥0 → Ω → ℝ≥0)
    (hX : IsLevyProcess X P)
    (hτ : IsLevyProcess (fun t ω => (τ t ω : ℝ)) P)
    (hmon : ∀ᵐ ω ∂P, Monotone (fun t => τ t ω))
    (hind : iIndepFun (fun (i : Fin 2) (ω : Ω) => fun t : ℝ≥0 =>
      if i = 0 then X t ω else (τ t ω : ℝ)) P)
    (s u : ℝ≥0) (hsu : s ≤ u)
    (H : ℝ → ℂ) (hH : Measurable H)
    (C : ℝ) (hC : ∀ x, ‖H x‖ ≤ C) :
    AEMeasurable (fun ω => X (τ u ω) ω - X (τ s ω) ω) P ∧
    (∫ ω, H (X (τ u ω) ω - X (τ s ω) ω) ∂P) =
      ∫ ω, (∫ ω', H (X (((τ u ω : ℝ) - (τ s ω : ℝ)).toNNReal) ω') ∂P) ∂P := by sorry
