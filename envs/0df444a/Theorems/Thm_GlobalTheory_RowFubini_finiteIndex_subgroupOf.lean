-- Prove2me | Theorems.Thm_GlobalTheory_RowFubini_finiteIndex_subgroupOf
-- name    : GlobalTheory.RowFubini.finiteIndex_subgroupOf
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T19:30:39.987798+00:00
-- url     : https://prove2.me/theorems/c47775be-e2b9-4728-8db0-3fa4365b12d3
-- title:
--   Row Fubini: finite Index subgroup Of
-- statement:
--   The Row Fubini construction uses the finite Index subgroup Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HaarTraceConjEqConstMulKernelImage.lean#L60-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HaarTraceConjEqConstMulKernelImage.lean#L60-L66

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HaarTraceConjEqConstMulKernelImage
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped Pointwise ENNReal
open GlobalTheory GlobalTheory.RowFubini
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G]

theorem GlobalTheory.RowFubini.finiteIndex_subgroupOf (H L : Subgroup G) (hH : IsOpen (H : Set G))
    (hL : IsCompact (L : Set G)) : (H.subgroupOf L).FiniteIndex := by sorry
