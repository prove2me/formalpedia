-- Prove2me | Theorems.Thm_GlobalTheory_SgAlg_WittField_cT_mul
-- name    : GlobalTheory.SgAlg.WittField.cT_mul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:54:36.582843+00:00
-- url     : https://prove2.me/theorems/4ebe89ab-33dc-4d26-949b-948a1dded100
-- title:
--   Witt Field: c T mul
-- statement:
--   The Witt Field construction uses the c T mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/WittExtensionHermitianFrames.lean#L74-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/WittExtensionHermitianFrames.lean#L74-L76

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

theorem GlobalTheory.SgAlg.WittField.cT_mul (A B : Matrix (Fin n) (Fin n) E) : cT σ (A * B) = cT σ B * cT σ A := by sorry
