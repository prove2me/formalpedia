-- Prove2me | Theorems.Thm_Kyprianou_Ch03_reflectionStoppedMeasurableKernelV1
-- name    : Kyprianou.Ch03.reflectionStoppedMeasurableKernelV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T19:00:51.788633+00:00
-- url     : https://prove2.me/theorems/2b537236-8338-46df-a5a2-343041cbff66
-- title:
--   Strong Markov factor for a measurable stopped-state path kernel
-- statement:
--   On the finite stopped event, the joint law of a stopped-measurable real state and the shifted path is a product of the restricted state law and the fresh path law. This follows from the proved restricted strong Markov law on intersections with state preimages. Integrate a bounded measurable kernel against the product law.
-- source:
--   Kyprianou (2006), Exercise 3.2, stopped-state strong Markov transition kernel.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Definitions.Def_LevyExtrema_SBA_runSup
import Definitions.Def_Kyprianou_Ch03_ReflectedProcesses
open MeasureTheory ProbabilityTheory Filter Kyprianou.Ch03
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch03.reflectionStoppedMeasurableKernelV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → ℝ) (hX : IsLevyProcess X P)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (hNatural : IsCompletedNaturalFiltration P X F)
    (tau : Omega → WithTop NNReal) (hTau : IsStoppingTime F tau)
    (finiteTime : Omega → NNReal)
    (hFinite : ∀ w, tau w ≠ ⊤ → tau w = (finiteTime w : WithTop NNReal))
    (A : Set Omega)
    (hA : ∀ s : NNReal, MeasurableSet[F s]
      (A ∩ {w | tau w ≤ (s : WithTop NNReal)}))
    (S : Omega → ℝ)
    (hS : ∀ B : Set ℝ, MeasurableSet B → ∀ s : NNReal,
      MeasurableSet[F s] ({w | S w ∈ B} ∩ {w | tau w ≤ (s : WithTop NNReal)}))
    (H : ℝ × (NNReal → ℝ) → ℝ) (hH : Measurable H)
    (hBound : ∃ C : ℝ, 0 ≤ C ∧ ∀ z, |H z| ≤ C) :
    (∫ w in A ∩ {w | tau w ≠ ⊤},
      H (S w, fun u => X (finiteTime w + u) w - X (finiteTime w) w) ∂P) =
    (∫ w in A ∩ {w | tau w ≠ ⊤},
      (∫ eta, H (S w, fun u => X u eta) ∂P) ∂P) := by sorry
