-- Prove2me | Theorems.Thm_Kyprianou_Ch03_exercise32ReflectionsStrongMarkov
-- name    : Kyprianou.Ch03.exercise32ReflectionsStrongMarkov
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T09:49:43.077044+00:00
-- url     : https://prove2.me/theorems/612fd176-5f54-4175-839f-3a1c07fd8378
-- title:
--   Exercise 3.2: strong Markov property of both reflected Lévy processes
-- statement:
--   Exact random-time Markov transition identities for both nonnegative reflected processes, conditional on any stopped-past event; bounded measurable test functions ensure expectations exist. Solution uses post-stopping increments and right-continuity.
-- source:
--   Kyprianou (2006), Exercise 3.2, p. 83; solution pp. 312–313.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Definitions.Def_LevyExtrema_SBA_runSup
import Definitions.Def_Kyprianou_Ch03_ReflectedProcesses
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

theorem exercise32ReflectionsStrongMarkov
{Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal → Omega → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hNatural : IsCompletedNaturalFiltration P X F)
    (y : ℝ) (hy : 0 ≤ y)
    (tau : Omega → WithTop NNReal) (hTau : IsStoppingTime F tau)
    (finiteTime : Omega → NNReal)
    (hFinite : ∀ omega, tau omega ≠ ⊤ →
      tau omega = (finiteTime omega : WithTop NNReal)) :
    ∀ A : Set Omega,
      (∀ s : NNReal, MeasurableSet[F s]
        (A ∩ {omega : Omega | tau omega ≤ (s : WithTop NNReal)})) →
      ∀ f : ℝ → ℝ, Measurable f →
        (∃ C : ℝ, 0 ≤ C ∧ ∀ z, |f z| ≤ C) →
        ∀ t : NNReal,
          (∫ omega in A ∩ {omega | tau omega ≠ ⊤},
            f (reflectedSup X y (finiteTime omega + t) omega) ∂P) =
          (∫ omega in A ∩ {omega | tau omega ≠ ⊤},
            (∫ eta,
              f (max (reflectedSup X y (finiteTime omega) omega)
                    (LevyExtrema.SBA.runSup (fun s => X s eta) t) -
                    X t eta) ∂P) ∂P) ∧
          (∫ omega in A ∩ {omega | tau omega ≠ ⊤},
            f (reflectedInf X y (finiteTime omega + t) omega) ∂P) =
          (∫ omega in A ∩ {omega | tau omega ≠ ⊤},
            (∫ eta,
              f (max (reflectedInf X y (finiteTime omega) omega)
                    (LevyExtrema.SBA.runSup (fun s => -(X s eta)) t) +
                    X t eta) ∂P) ∂P) := by
  sorry

end Kyprianou.Ch03
