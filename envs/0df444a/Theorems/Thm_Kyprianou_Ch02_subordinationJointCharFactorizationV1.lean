-- Prove2me | Theorems.Thm_Kyprianou_Ch02_subordinationJointCharFactorizationV1
-- name    : Kyprianou.Ch02.subordinationJointCharFactorizationV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T00:03:49.885491+00:00
-- url     : https://prove2.me/theorems/5d16d881-2608-4bf8-876e-21f27f090298
-- title:
--   subordinationJointCharFactorizationV1
-- statement:
--   subordinationJointCharFactorizationV1
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.15

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.subordinationJointCharFactorizationV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (τ : ℝ≥0 → Ω → ℝ≥0)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hτ : ProbabilityTheory.IsLevyProcess (fun t ω => (τ t ω : ℝ)) P)
    (hmon : ∀ᵐ ω ∂P, Monotone (fun t => τ t ω))
    (hind : ProbabilityTheory.iIndepFun
       (fun (i : Fin 2) (ω : Ω) => fun t : ℝ≥0 =>
         if i = 0 then X t ω else (τ t ω : ℝ)) P)
    (n : ℕ) (t : Fin (n+1) → ℝ≥0) (ht : Monotone t) (θ : Fin n → ℝ) :
    (∫ ω, ∏ k : Fin n, Complex.exp ((θ k : ℂ) *
      (increment (fun t ω => X (τ t ω) ω) (t k.castSucc) (t k.succ) ω : ℂ) * Complex.I) ∂P) =
    ∏ k : Fin n, charFun (P.map (increment (fun t ω => X (τ t ω) ω)
      (t k.castSucc) (t k.succ))) (θ k) := by sorry
