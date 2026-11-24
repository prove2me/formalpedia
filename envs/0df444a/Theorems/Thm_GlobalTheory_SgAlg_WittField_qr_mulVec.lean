-- Prove2me | Theorems.Thm_GlobalTheory_SgAlg_WittField_qr_mulVec
-- name    : GlobalTheory.SgAlg.WittField.qr_mulVec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:09:32.685858+00:00
-- url     : https://prove2.me/theorems/57b2ba8c-5070-4294-9193-03f8a518f974
-- title:
--   Witt Field: qr mul Vec
-- statement:
--   The Witt Field construction uses the qr mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/WittExtensionHermitianFrames.lean#L90-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/WittExtensionHermitianFrames.lean#L90-L95

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

theorem GlobalTheory.SgAlg.WittField.qr_mulVec (u : Fin n → E) (l : E) (v : Fin n → E) :
    qr σ J u l *ᵥ v = v - (l * form σ J v u) • u := by sorry
