-- Prove2me | Theorems.Thm_GlobalTheory_iInf_sup_pow_eq_of_compatible
-- name    : GlobalTheory.iInf_sup_pow_eq_of_compatible
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:55:21.635334+00:00
-- url     : https://prove2.me/theorems/08e600c9-6816-4401-80c1-abcab4409a3e
-- title:
--   Global Theory: i Inf sup pow eq of compatible
-- statement:
--   The Global Theory construction uses the i Inf sup pow eq of compatible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IInfSupPowEqOfAdicCompatibleIdeals.lean#L6-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IInfSupPowEqOfAdicCompatibleIdeals.lean#L6-L15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IInfSupPowEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IInfSupPowEqOfAdicCompatibleIdeals
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.iInf_sup_pow_eq_of_compatible :
    ∀ (C : Type) [CommRing C] (J : Ideal C), IsAdicComplete J C → ∀ u : ℕ → Ideal C,
      (∀ e, u e = u (e + 1) ⊔ J ^ (e + 1)) → ∀ e, (⨅ l, u l) ⊔ J ^ (e + 1) = u e := by sorry
