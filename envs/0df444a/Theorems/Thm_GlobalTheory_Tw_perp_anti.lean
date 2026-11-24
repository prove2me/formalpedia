-- Prove2me | Theorems.Thm_GlobalTheory_Tw_perp_anti
-- name    : GlobalTheory.Tw.perp_anti
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:13:27.703592+00:00
-- url     : https://prove2.me/theorems/6502bdc7-db55-4064-accd-44ca1ea88794
-- title:
--   Tw: perp anti
-- statement:
--   The Tw construction uses the perp anti property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsHermitianOfMemRealScalars.lean#L281-L281
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsHermitianOfMemRealScalars.lean#L281-L281

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemCentIffTwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsHermitianOfMemRealScalars
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open GlobalTheory GlobalTheory.Tw
variable {n : ℕ}

theorem GlobalTheory.Tw.perp_anti {V V' : Submodule ℂ (Fin n → ℂ)} (h : V ≤ V') : perp V' ≤ perp V := by sorry
