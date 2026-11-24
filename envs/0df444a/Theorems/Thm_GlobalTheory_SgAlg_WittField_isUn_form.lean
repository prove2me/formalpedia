-- Prove2me | Theorems.Thm_GlobalTheory_SgAlg_WittField_isUn_form
-- name    : GlobalTheory.SgAlg.WittField.isUn_form
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:54:47.163951+00:00
-- url     : https://prove2.me/theorems/646f600d-b4bc-4c2f-80a5-fb94882d5418
-- title:
--   Witt Field: is Un form
-- statement:
--   The Witt Field construction uses the is Un form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/WittExtensionHermitianFrames.lean#L53-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/WittExtensionHermitianFrames.lean#L53-L55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_InFrameStabilizer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittExtensionHermitianFrames
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.SgAlg GlobalTheory.SgAlg.WittField
variable {E : Type} [Field E] {σ : E →+* E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem GlobalTheory.SgAlg.WittField.isUn_form {g : Matrix (Fin n) (Fin n) E} (hg : IsUn σ J g) (v w : Fin n → E) :
    form σ J (g *ᵥ v) (g *ᵥ w) = form σ J v w := by sorry
