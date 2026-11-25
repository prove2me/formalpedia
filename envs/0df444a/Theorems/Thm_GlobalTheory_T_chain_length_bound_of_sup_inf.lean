-- Prove2me | Theorems.Thm_GlobalTheory_T_chain_length_bound_of_sup_inf
-- name    : GlobalTheory.T.chain_length_bound_of_sup_inf
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:27:11.045203+00:00
-- url     : https://prove2.me/theorems/ba11dc42-ada8-4376-9477-ec43a80659f8
-- title:
--   T: chain length bound of sup inf
-- statement:
--   The T construction uses the chain length bound of sup inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ChainLengthBoundOfSupInfStatement.lean#L6-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ChainLengthBoundOfSupInfStatement.lean#L6-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ChainLengthBoundOfSupInf
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ChainLengthBoundOfSupInfStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.chain_length_bound_of_sup_inf : ∀ {α : Type} [Lattice α] [IsModularLattice α] (C : α) (Q Q1 Q2 : α → Prop) (L1 L2 : ℕ),
    (∀ x, Q x → Q1 (x ⊓ C)) → (∀ x, Q x → Q2 (x ⊔ C)) →
    (∀ (r : ℕ) (N : Fin r → α), StrictMono N → (∀ i, Q1 (N i)) → r ≤ L1) →
    (∀ (r : ℕ) (N : Fin r → α), StrictMono N → (∀ i, Q2 (N i)) → r ≤ L2) →
    ∀ (r : ℕ) (N : Fin r → α), StrictMono N → (∀ i, Q (N i)) → r ≤ L1 + L2 := by sorry
