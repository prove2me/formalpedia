-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_maximal_operatorStable_of_finset_generating
-- name    : GlobalTheory.T.exists_maximal_operatorStable_of_finset_generating
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T20:36:48.146742+00:00
-- url     : https://prove2.me/theorems/2e35103e-cdc0-4be8-af7b-73320026694f
-- title:
--   T: exists maximal operator Stable of finset generating
-- statement:
--   The T construction uses the exists maximal operator Stable of finset generating property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsMaximalOperatorStableOfFinsetGeneratingStatement.lean#L8-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsMaximalOperatorStableOfFinsetGeneratingStatement.lean#L8-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsMaximalOperatorStableOfFinsetGenerating
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsMaximalOperatorStableOfFinsetGeneratingStatement
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

theorem GlobalTheory.T.exists_maximal_operatorStable_of_finset_generating : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] (G : Set (Module.End ℂ V)) (R : Submodule ℂ V)
    (F : Finset V),
    (∀ N : Submodule ℂ V, R ≤ N → GlobalTheory.TensHead.Stab G N → (↑F : Set V) ⊆ ↑N → N = ⊤) →
    ∀ N : Submodule ℂ V, R ≤ N → GlobalTheory.TensHead.Stab G N → N ≠ ⊤ →
      ∃ N' : Submodule ℂ V, N ≤ N' ∧ GlobalTheory.TensHead.Stab G N' ∧ N' ≠ ⊤ ∧
        ∀ U : Submodule ℂ V, GlobalTheory.TensHead.Stab G U → N' ≤ U → U = N' ∨ U = ⊤ := by sorry
