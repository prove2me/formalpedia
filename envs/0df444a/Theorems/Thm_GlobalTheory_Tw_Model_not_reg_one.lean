-- Prove2me | Theorems.Thm_GlobalTheory_Tw_Model_not_reg_one
-- name    : GlobalTheory.Tw.Model.not_reg_one
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:41:55.241255+00:00
-- url     : https://prove2.me/theorems/edbe2a3e-6574-41bc-abba-ef578b3d5246
-- title:
--   Model: not reg one
-- statement:
--   The Model construction uses the not reg one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/MemCentIffTwConj.lean#L126-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/MemCentIffTwConj.lean#L126-L130

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemCentIffTwConj
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
open GlobalTheory GlobalTheory.Tw GlobalTheory.Tw.Model
variable {n : ℕ} {R : Type} [CommRing R] [StarRing R]

theorem GlobalTheory.Tw.Model.not_reg_one : ¬ Reg (1 : Matrix (Fin 2) (Fin 2) ℂ) := by sorry
