-- Prove2me | Theorems.Thm_Kyprianou_Ch01_measurableInverseReciprocalOccupationFromSections
-- name    : Kyprianou.Ch01.measurableInverseReciprocalOccupationFromSections
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T22:10:33.518947+00:00
-- url     : https://prove2.me/theorems/2dc7607e-9030-4adc-a4f2-df34dd1edc17
-- title:
--   Measurable reciprocal-occupation right inverse from measurable monotone clock sections
-- statement:
--   Every reciprocalOccupation clock is monotone in NNReal physical time by already Proved Kyprianou.Ch01.reciprocalOccupationMonotone. Assume all its physical-time sections are measurable random variables. Show the source inverseReciprocalOccupation X t ω, defined as the WithTop NNReal infimum of physical times s where (t:ENNReal) < reciprocalOccupation X s ω, is measurable for every inverse level t. Use monotonicity: any strict upper crossing remains a crossing at later times, so the real-time hitting-set infimum equals the infimum over a countable dense family of nonnegative rational physical times. Each rational crossing event is measurable by hMeas, each WithTop-valued conditional clock is measurable, and countable iInf is measurable. Handle empty crossing set as top. No right continuity is needed for the monotone strict-crossing-set argument, including ENNReal infinity and no-explosion case.
-- source:
--   Kyprianou (2006) §1.3.4 original reverse Lamperti definition Def_Kyprianou_Ch01_LampertiInverse. Canonical reverse theorem ac1b29c6-5525-4344-a03d-7469824736ed, accepted joint-clock sketch b5a9603d-ed83-42a6-a4f8-58d01ffcab00, accepted stopped-clock sketch c27b9d45-466f-43ce-adcf-f9368d7f292f. Target root-connected inverse clock version f852e790-8678-45eb-9775-7f5af1318dd3. Reuse Proved reciprocalOccupationMonotone d401e83a-e957-4235-98fe-1c200c964b6e and existing Proved rationalStrictUpperPassageInfMeasurablePublic 8d95af79-d7ab-43bf-844a-306c13414921 as a pattern; new mathematical work is monotone strict passage rational cofinality.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.measurableInverseReciprocalOccupationFromSections
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℤ)
    (hMeas : ∀ s : ℝ≥0,
      Measurable (fun ω : Ω => reciprocalOccupation X s ω)) :
    ∀ t : ℝ≥0,
      Measurable (fun ω : Ω => inverseReciprocalOccupation X t ω) := by
  sorry
