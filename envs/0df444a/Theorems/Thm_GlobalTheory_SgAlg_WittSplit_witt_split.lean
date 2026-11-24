-- Prove2me | Theorems.Thm_GlobalTheory_SgAlg_WittSplit_witt_split
-- name    : GlobalTheory.SgAlg.WittSplit.witt_split
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T19:54:41.014812+00:00
-- url     : https://prove2.me/theorems/4ffe5a3d-be54-47e1-994a-716386a73a38
-- title:
--   Witt Split: witt split
-- statement:
--   The Witt Split construction uses the witt split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/WittFreeTuplesSplitQuadraticEtale.lean#L254-L303
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/WittFreeTuplesSplitQuadraticEtale.lean#L254-L303

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_InFrameStabilizer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittFreeTuplesSplitQuadraticEtale
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SgAlg Matrix Module
noncomputable section
open GlobalTheory GlobalTheory.SgAlg GlobalTheory.SgAlg.WittSplit

theorem GlobalTheory.SgAlg.WittSplit.witt_split : ∀ {E : Type} [CommRing E] (σ : E →+* E), IsQA σ →
    (∃ e : E, e * e = e ∧ e + σ e = 1 ∧ ∀ x : E, e * x ≠ 0 → ∃ y, e * x * y = e) →
    ∀ {n a : ℕ} (J : Matrix (Fin n) (Fin n) E), IsHermU σ J →
    ∀ (X X' : Matrix (Fin n) (Fin a) E), Free X → Free X' → pairM σ J X X = pairM σ J X' X' →
    ∃ g, IsUn σ J g ∧ g * X = X' := by sorry
