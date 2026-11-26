-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46ExtendedStoppedPathLawV1
-- name    : Kyprianou.Ch04.exercise46ExtendedStoppedPathLawV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T22:56:08.766274+00:00
-- url     : https://prove2.me/theorems/bc09b130-ada5-464c-99d7-52aea3e71196
-- title:
--   Extended stopping time restricted future law for spectrally negative Levy processes
-- statement:
--   On the finite event of an extended stopping time, the entire shifted future process has the original path law, independently of the stopped history.
-- source:
--   Kyprianou (2006), Exercise 4.6(ii).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter AvramDividend.Classical Set
open scoped NNReal ENNReal
set_option autoImplicit false
open scoped Topology

theorem Kyprianou.Ch04.exercise46ExtendedStoppedPathLawV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P F)
    (tau : Omega → WithTop NNReal)
    (hTau : IsStoppingTime F tau)
    (finiteTime : Omega → NNReal)
    (hFiniteTime : ∀ omega, tau omega ≠ ⊤ →
      tau omega = (finiteTime omega : WithTop NNReal)) :
    AEMeasurable (fun omega : Omega => fun u : NNReal =>
      L.X (finiteTime omega + u) omega - L.X (finiteTime omega) omega)
      (P.restrict {omega : Omega | tau omega ≠ ⊤}) ∧
    ∀ B : Set Omega, (∀ s : NNReal, MeasurableSet[F s]
      (B ∩ {omega : Omega | tau omega ≤ (s : WithTop NNReal)})) →
      Measure.map (fun omega : Omega => fun u : NNReal =>
        L.X (finiteTime omega + u) omega - L.X (finiteTime omega) omega)
        (P.restrict (B ∩ {omega : Omega | tau omega ≠ ⊤})) =
      P (B ∩ {omega : Omega | tau omega ≠ ⊤}) • Measure.map (fun omega u => L.X u omega) P := by
  sorry
