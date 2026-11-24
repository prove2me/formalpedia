-- Prove2me | Theorems.Thm_GlobalTheory_SgAlg_WittField_qr_form
-- name    : GlobalTheory.SgAlg.WittField.qr_form
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:17:22.412806+00:00
-- url     : https://prove2.me/theorems/613f3afb-b05c-45f4-8f53-42e94a521a2b
-- title:
--   Witt Field: qr form
-- statement:
--   The Witt Field construction uses the qr form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/WittExtensionHermitianFrames.lean#L97-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/WittExtensionHermitianFrames.lean#L97-L103

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

theorem GlobalTheory.SgAlg.WittField.qr_form (hσ : ∀ x, σ (σ x) = x) (hJ : cT σ J = J) (u : Fin n → E) (l : E)
    (hl : l * σ l * form σ J u u = l + σ l) (v w : Fin n → E) :
    form σ J (qr σ J u l *ᵥ v) (qr σ J u l *ᵥ w) = form σ J v w := by sorry
