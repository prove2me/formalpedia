-- Prove2me | Theorems.Thm_GlobalTheory_CompactAvgSchwartz_comp_mem_SB
-- name    : GlobalTheory.CompactAvgSchwartz.comp_mem_SB
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T16:59:31.649807+00:00
-- url     : https://prove2.me/theorems/6cbb9137-7385-48fc-9256-ebf2aa1c30e0
-- title:
--   Compact Avg Schwartz: comp mem SB
-- statement:
--   The Compact Avg Schwartz construction uses the comp mem SB property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsSchwartzIntegral.lean#L135-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsSchwartzIntegral.lean#L135-L150

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

theorem GlobalTheory.CompactAvgSchwartz.comp_mem_SB {a b : Y → Y} (ha : Continuous a) (hb : Continuous b) (h : ∀ y, b (a y) = y)
    (hg : g ∈ WeilM.SB Y) : (fun y => g (a y)) ∈ WeilM.SB Y := by sorry
