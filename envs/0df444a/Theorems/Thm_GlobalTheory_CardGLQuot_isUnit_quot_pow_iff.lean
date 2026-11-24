-- Prove2me | Theorems.Thm_GlobalTheory_CardGLQuot_isUnit_quot_pow_iff
-- name    : GlobalTheory.CardGLQuot.isUnit_quot_pow_iff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:21:04.864211+00:00
-- url     : https://prove2.me/theorems/64b3f5df-8037-4c8a-96ea-1750cbafcb62
-- title:
--   Card GLQuot: is Unit quot pow iff
-- statement:
--   The Card GLQuot construction uses the is Unit quot pow iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CardGLRingOfIntegersQuotientProdFactors.lean#L105-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CardGLRingOfIntegersQuotientProdFactors.lean#L105-L124

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RowBlockIndicatorFromLtIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardGLRingOfIntegersQuotientProdFactors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField UniqueFactorizationMonoid GlobalTheory.StdLoc
noncomputable section
open GlobalTheory GlobalTheory.CardGLQuot

theorem GlobalTheory.CardGLQuot.isUnit_quot_pow_iff {A : Type} [CommRing A] {w : Ideal A} (hw : w.IsMaximal) {c : ℕ} (hc : c ≠ 0)
    (x : A ⧸ w ^ c) : IsUnit x ↔ Ideal.Quotient.factor (Ideal.pow_le_self hc) x ≠ 0 := by sorry
