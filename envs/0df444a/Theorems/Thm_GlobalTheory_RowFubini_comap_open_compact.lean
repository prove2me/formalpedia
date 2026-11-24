-- Prove2me | Theorems.Thm_GlobalTheory_RowFubini_comap_open_compact
-- name    : GlobalTheory.RowFubini.comap_open_compact
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:16:06.00291+00:00
-- url     : https://prove2.me/theorems/f306f6c5-9408-458f-bb31-7c2e8d920e63
-- title:
--   Row Fubini: comap open compact
-- statement:
--   The Row Fubini construction uses the comap open compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HaarTraceConjEqConstMulKernelImage.lean#L118-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HaarTraceConjEqConstMulKernelImage.lean#L118-L122

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

theorem GlobalTheory.RowFubini.comap_open_compact (R Q : Subgroup X) (hR : IsClosed (R : Set X))
    (hQo : IsOpen (Q : Set X)) (hQc : IsCompact (Q : Set X)) :
    IsOpen ((Q.comap R.subtype : Subgroup R) : Set R) ∧
      IsCompact ((Q.comap R.subtype : Subgroup R) : Set R) := by sorry
