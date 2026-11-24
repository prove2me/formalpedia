-- Prove2me | Theorems.Thm_GlobalTheory_RowFubini_conjSub_open_compact
-- name    : GlobalTheory.RowFubini.conjSub_open_compact
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T19:30:30.198884+00:00
-- url     : https://prove2.me/theorems/b540f3b6-e31a-4aec-8b5e-312a2cd1e36f
-- title:
--   Row Fubini: conj Sub open compact
-- statement:
--   The Row Fubini construction uses the conj Sub open compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HaarTraceConjEqConstMulKernelImage.lean#L142-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HaarTraceConjEqConstMulKernelImage.lean#L142-L149

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
variable {X : Type*} [Group X] [TopologicalSpace X] [IsTopologicalGroup X]

theorem GlobalTheory.RowFubini.conjSub_open_compact (K : Subgroup X) (b : X) (hKo : IsOpen (K : Set X))
    (hKc : IsCompact (K : Set X)) :
    IsOpen (conjSub K b : Set X) ∧ IsCompact (conjSub K b : Set X) := by sorry
