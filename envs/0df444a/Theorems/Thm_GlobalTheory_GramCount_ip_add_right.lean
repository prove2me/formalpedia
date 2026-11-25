-- Prove2me | Theorems.Thm_GlobalTheory_GramCount_ip_add_right
-- name    : GlobalTheory.GramCount.ip_add_right
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:19:33.252837+00:00
-- url     : https://prove2.me/theorems/941614a4-a85a-4f69-bcf2-23dac2777056
-- title:
--   Gram Count: ip add right
-- statement:
--   The Gram Count construction uses the ip add right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/PrimOfIsUnitDet.lean#L21-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/PrimOfIsUnitDet.lean#L21-L22

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

theorem GlobalTheory.GramCount.ip_add_right (x y y' : Fin n → A) : ip c x (y + y') = ip c x y + ip c x y' := by sorry
