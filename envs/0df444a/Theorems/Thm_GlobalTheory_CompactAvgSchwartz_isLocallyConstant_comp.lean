-- Prove2me | Theorems.Thm_GlobalTheory_CompactAvgSchwartz_isLocallyConstant_comp
-- name    : GlobalTheory.CompactAvgSchwartz.isLocallyConstant_comp
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T17:00:53.754629+00:00
-- url     : https://prove2.me/theorems/01d164b2-b40a-4fc5-85c2-1e87b4ccbeef
-- title:
--   Compact Avg Schwartz: is Locally Constant comp
-- statement:
--   The Compact Avg Schwartz construction uses the is Locally Constant comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsSchwartzIntegral.lean#L152-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsSchwartzIntegral.lean#L152-L187

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhiBoundPartsOfRadicalParametrisation
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsSchwartzIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ContDiff Classical
open GlobalTheory GlobalTheory.CompactAvgSchwartz
variable {S Y : Type} [TopologicalSpace S] [TopologicalSpace Y] {a b : S → Y → Y} {g : Y → ℂ}

theorem GlobalTheory.CompactAvgSchwartz.isLocallyConstant_comp [CompactSpace S] (ha : Continuous fun p : S × Y => a p.1 p.2)
    (hb : Continuous fun p : S × Y => b p.1 p.2) (h : ∀ s y, b s (a s y) = y) (hg : g ∈ WeilM.SB Y) :
    IsLocallyConstant fun s y => g (a s y) := by sorry
