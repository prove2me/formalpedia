-- Prove2me | Theorems.Thm_GlobalTheory_EmbUnitBallConj_ext_tmul
-- name    : GlobalTheory.EmbUnitBallConj.ext_tmul
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:58:11.865728+00:00
-- url     : https://prove2.me/theorems/1de56542-a7b1-4a9c-9d5c-212b5bb3502e
-- title:
--   Emb Unit Ball Conj: ext tmul
-- statement:
--   The Emb Unit Ball Conj construction uses the ext tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PadicEmbeddingsConjugate.lean#L74-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PadicEmbeddingsConjugate.lean#L74-L75

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicEmbeddingsConjugate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.EmbUnitBallConj
variable {l : ℕ} [Fact l.Prime] {E : Type} [Field E]

theorem GlobalTheory.EmbUnitBallConj.ext_tmul (a : E →+* PadicAlgCl l) (c : ℚ_[l]) (x : E) : ext a (c ⊗ₜ x) = c • a x := by sorry
