-- Prove2me | Theorems.Thm_Kyprianou_Ch01_aemeasurableCadlagNaturalRandomTimeEvaluation
-- name    : Kyprianou.Ch01.aemeasurableCadlagNaturalRandomTimeEvaluation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T18:42:08.595575+00:00
-- url     : https://prove2.me/theorems/fa15311c-386d-41cf-b249-ed0816342762
-- title:
--   Almost-everywhere measurable observation of a càdlàg natural-valued process at a measurable random time
-- statement:
--   If a natural-number-valued process has a measurable section at every deterministic nonnegative time and almost surely càdlàg sample paths, then its real-valued observation at any globally measurable NNReal random time is almost everywhere measurable. Càdlàg implies right continuity at every time simultaneously on a single full-measure event. Since Nat is discrete, real coercion preserves right-continuity. Apply the new public real-valued random-time evaluation theorem to the cast process, using the measurability of the Nat-to-Real cast. This supports evaluating the original branching population process at the inverse Lamperti occupation clock without assuming global path regularity or finite offspring mean.
-- source:
--   Kyprianou (2006) Chapter 1 §1.3.4, forward Lamperti time-change path measurability. Directly depends on proved or in-verification Kyprianou.Ch01.aemeasurableRightContinuousRealRandomTimeEvaluation UUID 74ed6524-e545-40dc-bdb3-0bd5fb653135 and public LeanLevy IsCadlag definition. Addresses true original Open Kyprianou.Ch01.branchingToPoissonPathAEMeasurableFromCadlag UUID a50b477a-4a36-47b8-a220-857f6c082b64.

import Mathlib
import Definitions.Def_LeanLevy_Processes_Cadlag
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.aemeasurableCadlagNaturalRandomTimeEvaluation
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Y : ℝ≥0 → Ω → ℕ)
    (hMeas : ∀ t : ℝ≥0, Measurable (Y t))
    (hCadlag : ∀ᵐ ω ∂P,
      IsCadlag (fun t : ℝ≥0 => Y t ω))
    (T : Ω → ℝ≥0) (hT : Measurable T) :
    AEMeasurable (fun ω : Ω => (Y (T ω) ω : ℝ)) P := by
  sorry
