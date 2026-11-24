-- Prove2me | Theorems.Thm_Kyprianou_Ch02_iIndepFunOfExpProductV1
-- name    : Kyprianou.Ch02.iIndepFunOfExpProductV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T00:03:53.897405+00:00
-- url     : https://prove2.me/theorems/3ca25354-cdbe-43f5-b590-e87c4e98ab35
-- title:
--   iIndepFunOfExpProductV1
-- statement:
--   iIndepFunOfExpProductV1
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.15

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.iIndepFunOfExpProductV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (D : Fin n → Ω → ℝ) (hm : ∀ k, AEMeasurable (D k) P)
    (hf : ∀ θ : Fin n → ℝ, (∫ ω, ∏ k : Fin n, Complex.exp ((θ k : ℂ) *
      (D k ω : ℂ) * Complex.I) ∂P) = ∏ k : Fin n, charFun (P.map (D k)) (θ k)) :
    iIndepFun D P := by sorry
