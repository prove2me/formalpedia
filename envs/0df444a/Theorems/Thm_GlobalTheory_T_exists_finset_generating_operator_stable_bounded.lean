-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_finset_generating_operator_stable_bounded
-- name    : GlobalTheory.T.exists_finset_generating_operator_stable_bounded
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:35:23.775955+00:00
-- url     : https://prove2.me/theorems/e9ddc52b-fab8-4676-933a-99d85ac93e3b
-- title:
--   T: exists finset generating operator stable bounded
-- statement:
--   The T construction uses the exists finset generating operator stable bounded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsFinsetGeneratingOperatorStableBoundedStatement.lean#L8-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsFinsetGeneratingOperatorStableBoundedStatement.lean#L8-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsFinsetGeneratingOperatorStableBounded
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsFinsetGeneratingOperatorStableBoundedStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_finset_generating_operator_stable_bounded : ∀ {M : Type} [AddCommGroup M] [Module ℂ M] (Op : Set (Module.End ℂ M)) (Rel : Submodule ℂ M),
    (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ M), StrictMono N →
        (∀ j, Rel ≤ N j ∧ ∀ g ∈ Op, ∀ x ∈ N j, g x ∈ N j) → m ≤ L) →
    ∃ F : Finset M, ∀ N : Submodule ℂ M, Rel ≤ N → GlobalTheory.TensHead.Stab Op N → (↑F : Set M) ⊆ ↑N → N = ⊤ := by sorry
