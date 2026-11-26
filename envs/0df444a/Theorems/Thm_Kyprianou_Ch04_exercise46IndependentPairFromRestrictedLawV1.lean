-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46IndependentPairFromRestrictedLawV1
-- name    : Kyprianou.Ch04.exercise46IndependentPairFromRestrictedLawV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:27:08.73721+00:00
-- url     : https://prove2.me/theorems/06ed0a38-9647-4862-8f52-2724e0540878
-- title:
--   Product law from restricted future law on mark events
-- statement:
--   Evaluate the joint law on measurable rectangles using the restricted future law, then apply product measure extensionality.
-- source:
--   Kyprianou (2006), Exercise 4.6(ii).

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46IndependentPairFromRestrictedLawV1
    {Omega E F : Type} [MeasurableSpace Omega] [MeasurableSpace E] [MeasurableSpace F]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (J : Omega → E) (Z Y : Omega → F)
    (hJ : Measurable J) (hZ : AEMeasurable Z P) (hY : Measurable Y)
    (hLaw : ∀ B : Set E, MeasurableSet B →
      (P.restrict (J ⁻¹' B)).map Z = P (J ⁻¹' B) • P.map Y) :
    P.map (fun w => (J w, Z w)) = (P.map J).prod (P.map Y) := by
  sorry
