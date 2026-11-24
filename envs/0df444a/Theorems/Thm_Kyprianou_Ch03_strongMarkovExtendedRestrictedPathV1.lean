-- Prove2me | Theorems.Thm_Kyprianou_Ch03_strongMarkovExtendedRestrictedPathV1
-- name    : Kyprianou.Ch03.strongMarkovExtendedRestrictedPathV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T07:09:26.957788+00:00
-- url     : https://prove2.me/theorems/f441c06a-283e-4064-b4f5-099f01124b30
-- title:
--   Theorem 3.1: extended stopping-time restricted path law by right-grid approximation
-- statement:
--   Extend the deterministic restricted law to the finite part of an extended stopping time by strict upper dyadic approximations, countable clock fibres, finite-dimensional convergence using right continuity almost everywhere, and cylinder uniqueness. Establish a.e. measurability under the finite restriction.
-- source:
--   Kyprianou (2006), Theorem 3.1; exact parent 2623fefc-be31-45fd-9189-b00f2e50b331.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter
open Kyprianou.Ch03
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.strongMarkovExtendedRestrictedPathV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal → Omega → Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hNatural : IsCompletedNaturalFiltration P X F)
    (hDet : ∀ (s : NNReal) (B : Set Omega), MeasurableSet[F s] B →
      Measure.map (fun omega u => X (s + u) omega - X s omega) (P.restrict B) =
        P B • Measure.map (fun omega u => X u omega) P)
    (tau : Omega → WithTop NNReal)
    (hTau : IsStoppingTime F tau)
    (finiteTime : Omega → NNReal)
    (hFiniteTime : ∀ omega, tau omega ≠ ⊤ →
      tau omega = (finiteTime omega : WithTop NNReal)) :
    AEMeasurable (fun omega : Omega => fun u : NNReal =>
      X (finiteTime omega + u) omega - X (finiteTime omega) omega) (P.restrict {omega : Omega | tau omega ≠ ⊤}) ∧
    ∀ B : Set Omega, (∀ s : NNReal, MeasurableSet[F s]
      (B ∩ {omega : Omega | tau omega ≤ (s : WithTop NNReal)})) →
      Measure.map (fun omega : Omega => fun u : NNReal =>
      X (finiteTime omega + u) omega - X (finiteTime omega) omega)
        (P.restrict (B ∩ {omega : Omega | tau omega ≠ ⊤})) =
      P (B ∩ {omega : Omega | tau omega ≠ ⊤}) • Measure.map (fun omega u => X u omega) P := by
  sorry
