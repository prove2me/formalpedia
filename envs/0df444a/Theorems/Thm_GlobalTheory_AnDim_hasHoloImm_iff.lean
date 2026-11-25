-- Prove2me | Theorems.Thm_GlobalTheory_AnDim_hasHoloImm_iff
-- name    : GlobalTheory.AnDim.hasHoloImm_iff
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:36:17.794675+00:00
-- url     : https://prove2.me/theorems/7a3cde6d-0a08-4447-9228-5b48868692ce
-- title:
--   An Dim: has Holo Imm iff
-- statement:
--   The An Dim construction uses the has Holo Imm iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/PointDimensionLtProjectiveLine.lean#L170-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/PointDimensionLtProjectiveLine.lean#L170-L190

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsClosedOfIsAnalyticSubset
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__LogResolutionProjectiveLine_09840aae280abe50
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PointDimensionLtProjectiveLine_f9cea2a23bf32842
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions GlobalTheory.LogResInt Filter Topology
noncomputable section
open GlobalTheory.AnDim
variable {d : ℕ} {X : Type} [TopologicalSpace X]

theorem GlobalTheory.AnDim.hasHoloImm_iff (h : Published.AnalyticSetDimension) [CompactSpace X] [T2Space X]
    {A : FinHolAtlas d X} {T : Set X} (hT : A.IsAnalyticSubset T) {k : ℕ} :
    HasHoloImm A T k ↔ (k : WithBot ℕ∞) ≤ analyticDim A T := by sorry
