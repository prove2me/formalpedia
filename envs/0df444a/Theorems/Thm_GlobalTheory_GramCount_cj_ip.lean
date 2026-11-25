-- Prove2me | Theorems.Thm_GlobalTheory_GramCount_cj_ip
-- name    : GlobalTheory.GramCount.cj_ip
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:19:25.353243+00:00
-- url     : https://prove2.me/theorems/649eda65-1d79-57a0-9483-7d71e4fb77d1
-- title:
--   Gram Count: cj ip
-- statement:
--   The Gram Count construction uses the cj ip property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/PrimOfIsUnitDet.lean#L59-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/PrimOfIsUnitDet.lean#L59-L63

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimOfIsUnitDet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.GramCount
variable {A : Type} [CommRing A]
variable (c : A →+* A) {n : ℕ}

theorem GlobalTheory.GramCount.cj_ip (hc : ∀ u, c (c u) = u) (x y : Fin n → A) : c (ip c x y) = ip c y x := by sorry
