-- Prove2me | Theorems.Thm_GlobalTheory_modular_chain_bound_add
-- name    : GlobalTheory.modular_chain_bound_add
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:11:09.560309+00:00
-- url     : https://prove2.me/theorems/e3c664ab-6904-48a8-a849-6c061b0a2894
-- title:
--   Global Theory: modular chain bound add
-- statement:
--   The Global Theory construction uses the modular chain bound add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ChainLengthBoundOfSupInf.lean#L13-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ChainLengthBoundOfSupInf.lean#L13-L46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ChainLengthBoundOfSupInf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.modular_chain_bound_add {α : Type} [Lattice α] [IsModularLattice α] (C : α)
    (Q Q1 Q2 : α → Prop) (L1 L2 : ℕ)
    (hQ1 : ∀ x, Q x → Q1 (x ⊓ C)) (hQ2 : ∀ x, Q x → Q2 (x ⊔ C))
    (h1 : ∀ (r : ℕ) (N : Fin r → α), StrictMono N → (∀ i, Q1 (N i)) → r ≤ L1)
    (h2 : ∀ (r : ℕ) (N : Fin r → α), StrictMono N → (∀ i, Q2 (N i)) → r ≤ L2)
    (r : ℕ) (N : Fin r → α) (hN : StrictMono N) (hQ : ∀ i, Q (N i)) : r ≤ L1 + L2 := by sorry
