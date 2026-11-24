-- Prove2me | Theorems.Thm_Kyprianou_Ch02_subordinationIncrementProductMixtureV1
-- name    : Kyprianou.Ch02.subordinationIncrementProductMixtureV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:59:29.589332+00:00
-- url     : https://prove2.me/theorems/3cb90123-f947-4838-938b-6661e584c841
-- title:
--   Independent clock finite product increment test mixture
-- statement:
--   Disintegrate the bounded product test on the random-time vector. On the conull monotone clock event, deterministic Levy increments are independent and stationary. Factor their conditional product expectation into lag kernels.
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.15.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Complex Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.subordinationIncrementProductMixtureV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (τ : ℝ≥0 → Ω → ℝ≥0)
    (hX : IsLevyProcess X P)
    (hτ : IsLevyProcess (fun t ω => (τ t ω : ℝ)) P)
    (hmon : ∀ᵐ ω ∂P, Monotone (fun t => τ t ω))
    (hind : iIndepFun (fun (i : Fin 2) (ω : Ω) => fun t : ℝ≥0 =>
      if i = 0 then X t ω else (τ t ω : ℝ)) P)
    (n : ℕ) (t : Fin (n + 1) → ℝ≥0) (ht : Monotone t)
    (H : Fin n → ℝ → ℂ) (hH : ∀ i, Measurable (H i))
    (hC : ∀ i x, ‖H i x‖ ≤ 1) :
    (∫ ω, ∏ i, H i (X (τ (t i.succ) ω) ω - X (τ (t i.castSucc) ω) ω) ∂P) =
      ∫ ω, ∏ i, (∫ ω', H i
        (X (((τ (t i.succ) ω : ℝ) - (τ (t i.castSucc) ω : ℝ)).toNNReal) ω') ∂P) ∂P := by sorry
