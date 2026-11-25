-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_ColumnSupport_colE_inv_mul_affPt
-- name    : GlobalTheory.RootEx.ColumnSupport.colE_inv_mul_affPt
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:20:32.366665+00:00
-- url     : https://prove2.me/theorems/67e13385-4fbc-4826-aad1-e0c7f54611fa
-- title:
--   Column Support: col E inv mul aff Pt
-- statement:
--   The Column Support construction uses the col E inv mul aff Pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ColEInvMulAffPt.lean#L9-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ColEInvMulAffPt.lean#L9-L27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeSupportAndFourierRelation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ColEInvMulAffPt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.ColumnSupport

theorem GlobalTheory.RootEx.ColumnSupport.colE_inv_mul_affPt {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n]
    {c p : ℕ} (hp : p < c) (β : n → k) (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free (p + 1) rs} → k) (r : n) :
    (((colE c (p + 1) β)⁻¹).val * affPt (p + 1) x₀ e) (Sum.inl r) (Sum.inr ⟨p, by omega⟩) = -β r := by sorry
