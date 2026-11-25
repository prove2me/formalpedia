-- Prove2me | Theorems.Thm_GlobalTheory_T_iInf_sup_pow_eq_of_adic_compatible_ideals
-- name    : GlobalTheory.T.iInf_sup_pow_eq_of_adic_compatible_ideals
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:33:25.898352+00:00
-- url     : https://prove2.me/theorems/8884ff32-8bdb-4367-bdb4-b21560b4e9fe
-- title:
--   T: i Inf sup pow eq of adic compatible ideals
-- statement:
--   The T construction uses the i Inf sup pow eq of adic compatible ideals property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IInfSupPowEqOfAdicCompatibleIdealsStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IInfSupPowEqOfAdicCompatibleIdealsStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IInfSupPowEqOfAdicCompatibleIdeals
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IInfSupPowEqOfAdicCompatibleIdealsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.iInf_sup_pow_eq_of_adic_compatible_ideals : ∀ (C : Type) [CommRing C] (J : Ideal C), IsAdicComplete J C → ∀ u : ℕ → Ideal C, (∀ e, u e = u (e + 1) ⊔ J ^ (e + 1)) → ∀ e, (⨅ l, u l) ⊔ J ^ (e + 1) = u e := by sorry
