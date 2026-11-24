-- Prove2me | Theorems.Thm_GlobalTheory_SgAlg_WittField_single_entry
-- name    : GlobalTheory.SgAlg.WittField.single_entry
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T19:54:07.229796+00:00
-- url     : https://prove2.me/theorems/3b21d2cd-3231-44df-a018-39e01ead4897
-- title:
--   Witt Field: single entry
-- statement:
--   The Witt Field construction uses the single entry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/WittExtensionHermitianFrames.lean#L57-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/WittExtensionHermitianFrames.lean#L57-L64

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

theorem GlobalTheory.SgAlg.WittField.single_entry (M : Matrix (Fin n) (Fin n) E) (i j : Fin n) :
    (fun k => σ ((Pi.single i (1 : E) : Fin n → E) k)) ⬝ᵥ (M *ᵥ (Pi.single j (1 : E) : Fin n → E)) = M i j := by sorry
