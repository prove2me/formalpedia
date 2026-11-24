-- Prove2me | Theorems.Thm_Kyprianou_Ch03_rawRightGermRestrictedVersionLawV1
-- name    : Kyprianou.Ch03.rawRightGermRestrictedVersionLawV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T13:19:56.543449+00:00
-- url     : https://prove2.me/theorems/e6590710-4b80-4063-a772-b0ed5ad1fef0
-- title:
--   Restricted law of the future of a measurable version at the right germ
-- statement:
--   For each decreasing time s strictly above t, transfer A to the raw Y filtration at s and apply the deterministic restricted future law. The càdlàg paths give common coordinate convergence as s decreases to t; the proved restricted path-law limit theorem gives the result.
-- source:
--   Kyprianou (2006), Exercise 3.1: right continuity of the completed natural filtration.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch03.rawRightGermRestrictedVersionLawV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X Y : NNReal → Omega → ℝ) (hY : IsLevyProcess Y P)
    (hMeas : ∀ t, Measurable (Y t))
    (hEq : ∀ᵐ w ∂P, ∀ u, Y u w = X u w)
    (t : NNReal) (A : Set Omega)
    (hA : MeasurableSet[⨅ s : NNReal, ⨅ (_ : t < s), PerfCorrMSQ.natFiltr X s] A) :
    Measure.map (fun (w : Omega) (u : NNReal) => Y (t + u) w - Y t w) (P.restrict A) =
      P A • Measure.map (fun (w : Omega) (u : NNReal) => Y u w) P := by
  sorry
