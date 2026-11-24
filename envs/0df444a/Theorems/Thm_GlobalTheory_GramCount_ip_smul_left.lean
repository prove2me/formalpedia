-- Prove2me | Theorems.Thm_GlobalTheory_GramCount_ip_smul_left
-- name    : GlobalTheory.GramCount.ip_smul_left
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T13:58:59.255801+00:00
-- url     : https://prove2.me/theorems/c9faa365-91e2-4c28-a5d2-6c7e7bbbca6c
-- title:
--   Gram Count: ip smul left
-- statement:
--   The Gram Count construction uses the ip smul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/PrimOfIsUnitDet.lean#L33-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/PrimOfIsUnitDet.lean#L33-L38

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

theorem GlobalTheory.GramCount.ip_smul_left (a : A) (x y : Fin n → A) : ip c (a • x) y = a * ip c x y := by sorry
