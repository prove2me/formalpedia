-- Prove2me | Theorems.Thm_GlobalTheory_GramCount_ip_sub_left
-- name    : GlobalTheory.GramCount.ip_sub_left
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:20:02.526638+00:00
-- url     : https://prove2.me/theorems/f9955c14-7939-4624-a9b2-d10a7f426b17
-- title:
--   Gram Count: ip sub left
-- statement:
--   The Gram Count construction uses the ip sub left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/PrimOfIsUnitDet.lean#L24-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/PrimOfIsUnitDet.lean#L24-L25

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

theorem GlobalTheory.GramCount.ip_sub_left (x x' y : Fin n → A) : ip c (x - x') y = ip c x y - ip c x' y := by sorry
