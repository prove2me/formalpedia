-- Prove2me | Theorems.Thm_GlobalTheory_RowFubini_map_open_compact
-- name    : GlobalTheory.RowFubini.map_open_compact
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:16:07.331227+00:00
-- url     : https://prove2.me/theorems/ba141ef4-6ca3-48f9-a359-dcef596620b5
-- title:
--   Row Fubini: map open compact
-- statement:
--   The Row Fubini construction uses the map open compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HaarTraceConjEqConstMulKernelImage.lean#L124-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HaarTraceConjEqConstMulKernelImage.lean#L124-L134

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

theorem GlobalTheory.RowFubini.map_open_compact {Y : Type*} [Group Y] [TopologicalSpace Y] [IsTopologicalGroup Y]
    (A : Subgroup X) (π : X →* Y) (σ : Y →* X) (hπ : Continuous π) (hσ : Continuous σ)
    (hsec : ∀ y, π (σ y) = y) (hAo : IsOpen (A : Set X)) (hAc : IsCompact (A : Set X)) :
    IsOpen ((A.map π : Subgroup Y) : Set Y) ∧ IsCompact ((A.map π : Subgroup Y) : Set Y) := by sorry
