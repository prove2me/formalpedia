-- Prove2me | Theorems.Thm_GlobalTheory_WeilCriterion_exists_isInvariantRadon
-- name    : GlobalTheory.WeilCriterion.exists_isInvariantRadon
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T21:52:38.120975+00:00
-- url     : https://prove2.me/theorems/e965b857-be2a-4d61-91a3-fa966ee60d30
-- title:
--   Weil Criterion: exists is Invariant Radon
-- statement:
--   The Weil Criterion construction uses the exists is Invariant Radon property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/WeilCriterionInvariantMeasureHomogeneousSpace.lean#L132-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/WeilCriterionInvariantMeasureHomogeneousSpace.lean#L132-L182

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_InvariantRadonFibre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsBruhatFunctionClosedSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsUniqueHaarOfInvariantRadonOnCosets
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_WeilCriterionInvariantMeasureHomogeneousSpace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre Topology
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.WeilCriterion
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  (H : Subgroup G) [LocallyCompactSpace H]
variable [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)]

theorem GlobalTheory.WeilCriterion.exists_isInvariantRadon (hH : IsClosed (H : Set G))
    (hΔ : ∀ h : H, modularCharacterFun (h : G) = modularCharacterFun h) :
    ∃ μ : Measure (G ⧸ H), IsInvariantRadon H μ := by sorry
