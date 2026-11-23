-- Prove2me | Theorems.Thm_GlobalTheory_QuotientHaar_lintegral_cosetMeasure
-- name    : GlobalTheory.QuotientHaar.lintegral_cosetMeasure
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:36:23.41461+00:00
-- url     : https://prove2.me/theorems/fd2e3cf3-d7a3-4606-8a07-905336484c08
-- title:
--   Quotient Haar: lintegral coset Measure
-- statement:
--   The Quotient Haar construction uses the lintegral coset Measure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsUniqueHaarOfInvariantRadonOnCosets.lean#L35-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsUniqueHaarOfInvariantRadonOnCosets.lean#L35-L39

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

theorem GlobalTheory.QuotientHaar.lintegral_cosetMeasure (ν : Measure H) [ν.IsMulLeftInvariant] {f : G → ℝ≥0∞}
    (hf : Measurable f) (q : G ⧸ H) :
    ∫⁻ x, f x ∂(cosetMeasure H ν q) = fibreIntegral H ν f q := by sorry
