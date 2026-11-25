-- Prove2me | Theorems.Thm_GlobalTheory_T_card_le_finrank_sup_eigenspaces
-- name    : GlobalTheory.T.card_le_finrank_sup_eigenspaces
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:26:23.99785+00:00
-- url     : https://prove2.me/theorems/07fd8dee-ec4f-5607-ab31-07acf7dc7d56
-- title:
--   T: card le finrank sup eigenspaces
-- statement:
--   The T construction uses the card le finrank sup eigenspaces property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CardLeFinrankSupEigenspacesStatement.lean#L5-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CardLeFinrankSupEigenspacesStatement.lean#L5-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardLeFinrankSupEigenspaces
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardLeFinrankSupEigenspacesStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.card_le_finrank_sup_eigenspaces : ∀ (W : Type 1) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (O : Type) (T : O → Module.End ℂ W),
    (∀ a b, Commute (T a) (T b)) → ∀ (I : Type) [Fintype I] (ψ : I → O → ℂ), Function.Injective ψ →
    (∀ i, 1 ≤ Module.finrank ℂ (⨅ a, Module.End.eigenspace (T a) (ψ i a) : Submodule ℂ W)) →
    Fintype.card I ≤ Module.finrank ℂ (⨆ i, ⨅ a, Module.End.eigenspace (T a) (ψ i a) : Submodule ℂ W) := by sorry
