-- Prove2me | Theorems.Thm_Kyprianou_Ch03_stoppedRestrictedPathLawIntegralKernelV1
-- name    : Kyprianou.Ch03.stoppedRestrictedPathLawIntegralKernelV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T19:04:17.768141+00:00
-- url     : https://prove2.me/theorems/bfd92649-c7e4-44c1-a51c-843b0d1bc0e3
-- title:
--   Restricted path-law factorisation implies bounded integral kernel identity
-- statement:
--   The hypothesis gives the joint law of the stopped state and the future path by equality on measurable rectangles. Use pushforward change of variables and Fubini on the product of finite measures; boundedness guarantees integrability.
-- source:
--   Kyprianou (2006), Exercise 3.2: reflected Lévy processes are strong Markov.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Definitions.Def_LevyExtrema_SBA_runSup
import Definitions.Def_Kyprianou_Ch03_ReflectedProcesses
open MeasureTheory ProbabilityTheory Filter Set Kyprianou.Ch03
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch03.stoppedRestrictedPathLawIntegralKernelV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (E : Set Omega) (hE : MeasurableSet E)
    (S : Omega → ℝ) (U V : Omega → (NNReal → ℝ))
    (hS : AEMeasurable S (P.restrict E))
    (hU : AEMeasurable U (P.restrict E)) (hV : AEMeasurable V P)
    (hLaw : ∀ B : Set ℝ, MeasurableSet B →
      Measure.map U (P.restrict (E ∩ S ⁻¹' B)) =
        P (E ∩ S ⁻¹' B) • Measure.map V P)
    (k : ℝ × (NNReal → ℝ) → ℝ) (hk : Measurable k)
    (hb : ∃ C : ℝ, 0 ≤ C ∧ ∀ z, |k z| ≤ C) :
    (∫ w in E, k (S w, U w) ∂P) =
      ∫ w in E, (∫ v, k (S w, V v) ∂P) ∂P := by
  sorry
