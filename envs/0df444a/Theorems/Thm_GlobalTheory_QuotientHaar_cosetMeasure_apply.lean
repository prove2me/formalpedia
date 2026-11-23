-- Prove2me | Theorems.Thm_GlobalTheory_QuotientHaar_cosetMeasure_apply
-- name    : GlobalTheory.QuotientHaar.cosetMeasure_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:35:03.823556+00:00
-- url     : https://prove2.me/theorems/5961daed-d9ae-4e97-9de4-662103dc2abe
-- title:
--   Quotient Haar: coset Measure apply
-- statement:
--   The Quotient Haar construction uses the coset Measure apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsUniqueHaarOfInvariantRadonOnCosets.lean#L30-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsUniqueHaarOfInvariantRadonOnCosets.lean#L30-L33

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

theorem GlobalTheory.QuotientHaar.cosetMeasure_apply (ν : Measure H) [ν.IsMulLeftInvariant] (g : G) {s : Set G}
    (hs : MeasurableSet s) :
    cosetMeasure H ν (g : G ⧸ H) s = ν ((fun h : H => g * (h : G)) ⁻¹' s) := by sorry
