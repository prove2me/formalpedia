-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46FiniteRestartLawUnrestrictV1
-- name    : Kyprianou.Ch04.exercise46FiniteRestartLawUnrestrictV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T09:07:01.39061+00:00
-- url     : https://prove2.me/theorems/598e70d5-f0c5-4b5b-85e5-4157d8fb8aec
-- title:
--   Almost surely finite stopped clock yields unrestricted first restart law
-- statement:
--   An almost surely finite first-arrival clock has a full-measure finite event, so restricting to that event does not change the future path law or its almost-everywhere measurability.
-- source:
--   Kyprianou (2006), Exercise 4.6(ii).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46FiniteRestartLawUnrestrictV1
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (A : Omega → WithTop NNReal)
    (hFin : ∀ᵐ w ∂P, A w ≠ ⊤)
    (Z Y : Omega → E)
    (hZ : AEMeasurable Z (P.restrict {w | A w ≠ ⊤}))
    (B : Set Omega)
    (hLaw : (P.restrict (B ∩ {w | A w ≠ ⊤})).map Z =
      P (B ∩ {w | A w ≠ ⊤}) • P.map Y) :
    AEMeasurable Z P ∧ (P.restrict B).map Z = P B • P.map Y := by
  sorry
