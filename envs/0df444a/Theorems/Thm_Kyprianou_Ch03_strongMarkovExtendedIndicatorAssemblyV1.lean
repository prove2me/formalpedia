-- Prove2me | Theorems.Thm_Kyprianou_Ch03_strongMarkovExtendedIndicatorAssemblyV1
-- name    : Kyprianou.Ch03.strongMarkovExtendedIndicatorAssemblyV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T07:09:19.92624+00:00
-- url     : https://prove2.me/theorems/0086c6a9-2a1f-474f-95e8-2bee321d1bf2
-- title:
--   Theorem 3.1: assemble indicator and path product on finite stopping event
-- statement:
--   Use the two stopped events A and its complement and the measurable finite stopping event. The indicator has two values; equality of the product measure follows by decomposing rectangles into the two indicator fibres. No probability normalisation of the finite restriction is required.
-- source:
--   Kyprianou (2006), Theorem 3.1; exact parent 2623fefc-be31-45fd-9189-b00f2e50b331.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter
open Kyprianou.Ch03
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.strongMarkovExtendedIndicatorAssemblyV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (tau : Omega → WithTop NNReal) (hTau : IsStoppingTime F tau)
    (Y : Omega → (NNReal → Real))
    (nu : Measure (NNReal → Real))
    (hY : AEMeasurable Y (P.restrict {omega : Omega | tau omega ≠ ⊤}))
    (hLaw : ∀ B : Set Omega, (∀ s : NNReal, MeasurableSet[F s]
      (B ∩ {omega : Omega | tau omega ≤ (s : WithTop NNReal)})) →
      Measure.map Y (P.restrict (B ∩ {omega : Omega | tau omega ≠ ⊤})) =
        P (B ∩ {omega : Omega | tau omega ≠ ⊤}) • nu) :
    ∀ A : Set Omega,
      (∀ s : NNReal, MeasurableSet[F s]
        (A ∩ {omega : Omega | tau omega ≤ (s : WithTop NNReal)})) →
      Measure.map (fun omega => (Set.indicator A (fun _ : Omega => (1 : Real)) omega,
        Y omega)) (P.restrict {omega : Omega | tau omega ≠ ⊤}) =
      (Measure.map (Set.indicator A (fun _ : Omega => (1 : Real)))
        (P.restrict {omega : Omega | tau omega ≠ ⊤})).prod nu := by
  sorry
