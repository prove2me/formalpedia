-- Prove2me | Theorems.Thm_GlobalTheory_SgAlg_witt_free_field
-- name    : GlobalTheory.SgAlg.witt_free_field
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T19:54:03.847408+00:00
-- url     : https://prove2.me/theorems/1d10cfb2-4d1b-4db4-a359-7a14022d2c6f
-- title:
--   Sg Alg: witt free field
-- statement:
--   The Sg Alg construction uses the witt free field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/WittExtensionHermitianFrames.lean#L233-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/WittExtensionHermitianFrames.lean#L233-L248

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
open GlobalTheory.SgAlg Matrix

theorem GlobalTheory.SgAlg.witt_free_field : ∀ {E : Type} [Field E] (σ : E →+* E), IsQA σ → ∀ {n a : ℕ}
    (J : Matrix (Fin n) (Fin n) E), IsHermU σ J → ∀ (X X' : Matrix (Fin n) (Fin a) E), Free X →
    Free X' → pairM σ J X X = pairM σ J X' X' → ∃ g, IsUn σ J g ∧ g * X = X' := by sorry
