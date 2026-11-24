-- Prove2me | Theorems.Thm_GlobalTheory_SgAlg_WittField_qr_fix
-- name    : GlobalTheory.SgAlg.WittField.qr_fix
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:17:19.921805+00:00
-- url     : https://prove2.me/theorems/e3c66674-0a62-4bb1-944e-6ae283fc8a2a
-- title:
--   Witt Field: qr fix
-- statement:
--   The Witt Field construction uses the qr fix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/WittExtensionHermitianFrames.lean#L109-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/WittExtensionHermitianFrames.lean#L109-L111

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

theorem GlobalTheory.SgAlg.WittField.qr_fix (u : Fin n → E) (l : E) (y : Fin n → E) (hy : form σ J y u = 0) :
    qr σ J u l *ᵥ y = y := by sorry
