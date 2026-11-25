-- Prove2me | Theorems.Thm_GlobalTheory_T_hasSum_quotient_of_hasSum_mulEquiv_quotient
-- name    : GlobalTheory.T.hasSum_quotient_of_hasSum_mulEquiv_quotient
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:32:28.467381+00:00
-- url     : https://prove2.me/theorems/3a2b42cd-d0e4-589b-a938-116399641b83
-- title:
--   T: has Sum quotient of has Sum mul Equiv quotient
-- statement:
--   The T construction uses the has Sum quotient of has Sum mul Equiv quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HasSumQuotientTransportStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HasSumQuotientTransportStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasSumQuotientTransport
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasSumQuotientTransportStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.hasSum_quotient_of_hasSum_mulEquiv_quotient : ∀ (G H : Type) [Group G] [Group H] (e : G ≃* H) (K : Subgroup G) (K' : Subgroup H), (∀ g, g ∈ K ↔ e g ∈ K') → ∀ f : G → ℂ, (∀ g, ∀ k ∈ K, f (g * k) = f g) → ∀ s : ℂ, HasSum (fun b : H ⧸ K' => f (e.symm b.out)) s → HasSum (fun a : G ⧸ K => f a.out) s := by sorry
