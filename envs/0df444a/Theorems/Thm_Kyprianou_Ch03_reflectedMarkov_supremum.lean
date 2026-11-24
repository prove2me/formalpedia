-- Prove2me | Theorems.Thm_Kyprianou_Ch03_reflectedMarkov_supremum
-- name    : Kyprianou.Ch03.reflectedMarkov_supremum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T15:00:32.929972+00:00
-- url     : https://prove2.me/theorems/cc6ea338-8a80-4e12-848b-ee635076ad6c
-- title:
--   Exercise 3.2 reflected processes clause 1
-- statement:
--   Independent full-strength supremum clause preserving all the original quantified assumptions and process models.
-- source:
--   Kyprianou (2006), first edition, Chapter 3, Exercise 3.2 reflected processes

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Definitions.Def_LevyExtrema_SBA_runSup
import Definitions.Def_Kyprianou_Ch03_ReflectedProcesses
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

theorem reflectedMarkov_supremum
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
                    X t eta) ∂P) ∂P) := by
  sorry

end Kyprianou.Ch03
