-- Prove2me | Theorems.Thm_Kyprianou_Ch02_independentRandomTimeVectorIntegralV1
-- name    : Kyprianou.Ch02.independentRandomTimeVectorIntegralV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:51:31.448838+00:00
-- url     : https://prove2.me/theorems/9de288e5-fedb-4399-9cc0-4faa938361d2
-- title:
--   Independent random-time vector evaluation and integral disintegration
-- statement:
--   A measurable universal evaluator and almost-everywhere measurable path maps allow the independent clock and path laws to be integrated over their product. The evaluator equals the actual values on the conull set of right-continuous paths; Fubini gives the asserted mixture for bounded measurable tests.
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.15; independent random-time integration.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Complex Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.independentRandomTimeVectorIntegralV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (τ : ℝ≥0 → Ω → ℝ≥0)
    (hX : IsLevyProcess X P)
    (hτ : IsLevyProcess (fun t ω => (τ t ω : ℝ)) P)
    (hind : iIndepFun (fun (i : Fin 2) (ω : Ω) => fun t : ℝ≥0 =>
      if i = 0 then X t ω else (τ t ω : ℝ)) P)
    (m : ℕ) (t : Fin m → ℝ≥0)
    (G : (Fin m → ℝ) → ℂ) (hG : Measurable G) :
    AEMeasurable (fun ω => fun i : Fin m => X (τ (t i) ω) ω) P ∧
    (∀ C : ℝ, (∀ x, ‖G x‖ ≤ C) →
      (∫ ω, G (fun i => X (τ (t i) ω) ω) ∂P) =
        ∫ ω, (∫ ω', G (fun i => X (τ (t i) ω) ω') ∂P) ∂P) := by sorry
