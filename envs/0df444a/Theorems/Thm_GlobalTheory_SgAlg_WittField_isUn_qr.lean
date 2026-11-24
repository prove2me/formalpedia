-- Prove2me | Theorems.Thm_GlobalTheory_SgAlg_WittField_isUn_qr
-- name    : GlobalTheory.SgAlg.WittField.isUn_qr
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:16:29.594257+00:00
-- url     : https://prove2.me/theorems/e51f08a1-7545-4294-84cb-43d86bc05176
-- title:
--   Witt Field: is Un qr
-- statement:
--   The Witt Field construction uses the is Un qr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/WittExtensionHermitianFrames.lean#L105-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/WittExtensionHermitianFrames.lean#L105-L107

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

theorem GlobalTheory.SgAlg.WittField.isUn_qr (hσ : ∀ x, σ (σ x) = x) (hJ : cT σ J = J) (u : Fin n → E) (l : E)
    (hl : l * σ l * form σ J u u = l + σ l) : IsUn σ J (qr σ J u l) := by sorry
