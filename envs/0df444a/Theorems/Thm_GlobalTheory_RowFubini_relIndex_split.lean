-- Prove2me | Theorems.Thm_GlobalTheory_RowFubini_relIndex_split
-- name    : GlobalTheory.RowFubini.relIndex_split
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:30:38.520253+00:00
-- url     : https://prove2.me/theorems/4488768c-3a79-46fd-a05e-617eb08e0575
-- title:
--   Row Fubini: rel Index split
-- statement:
--   The Row Fubini construction uses the rel Index split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HaarTraceConjEqConstMulKernelImage.lean#L22-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HaarTraceConjEqConstMulKernelImage.lean#L22-L49

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

theorem GlobalTheory.RowFubini.relIndex_split {G Y : Type*} [Group G] [Group Y] (π : G →* Y) (A B : Subgroup G)
    (hBA : B ≤ A) :
    B.relIndex A = B.relIndex (A ⊓ π.ker) * (B.map π).relIndex (A.map π) := by sorry
