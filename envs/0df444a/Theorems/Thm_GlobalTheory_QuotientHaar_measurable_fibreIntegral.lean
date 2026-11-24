-- Prove2me | Theorems.Thm_GlobalTheory_QuotientHaar_measurable_fibreIntegral
-- name    : GlobalTheory.QuotientHaar.measurable_fibreIntegral
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:12:19.333853+00:00
-- url     : https://prove2.me/theorems/9d040437-dadd-4561-baef-d82f8d2e6919
-- title:
--   Quotient Haar: measurable fibre Integral
-- statement:
--   The Quotient Haar construction uses the measurable fibre Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsUniqueHaarOfInvariantRadonOnCosets.lean#L108-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsUniqueHaarOfInvariantRadonOnCosets.lean#L108-L114

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_InvariantRadonFibre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsUniqueHaarOfInvariantRadonOnCosets
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal Pointwise
open GlobalTheory GlobalTheory.QuotientHaar
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] (H : Subgroup G)
variable [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]

theorem GlobalTheory.QuotientHaar.measurable_fibreIntegral (hH : IsClosed (H : Set G)) (ν : Measure H)
    [ν.IsHaarMeasure] [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)] {f : G → ℝ≥0∞}
    (hf : Measurable f) : Measurable (fibreIntegral H ν f) := by sorry
