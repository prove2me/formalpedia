-- Prove2me | Theorems.Thm_GlobalTheory_ValuedPrincipal_exists_least_of_discrete
-- name    : GlobalTheory.ValuedPrincipal.exists_least_of_discrete
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T21:50:40.450307+00:00
-- url     : https://prove2.me/theorems/bfaf08fa-de4c-46b2-b302-fadeb03ea918
-- title:
--   Valued Principal: exists least of discrete
-- statement:
--   The Valued Principal construction uses the exists least of discrete property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/ExistsLeastOfDiscrete.lean#L75-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/ExistsLeastOfDiscrete.lean#L75-L111

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExistsLeastOfDiscrete
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ValuedPrincipal
variable {F : Type} [Field F] (v : AddValuation F (WithTop ℚ))

theorem GlobalTheory.ValuedPrincipal.exists_least_of_discrete {π : F} (hπ : v π = ((1 : ℚ) : WithTop ℚ)) {d : ℕ} (hd : 1 ≤ d)
    (h : ∀ x : F, x ≠ 0 → ∃ n : ℤ, v x = (((n : ℚ) / d : ℚ) : WithTop ℚ)) (q : ℚ) :
    ∃ t : F, t ≠ 0 ∧ (q : WithTop ℚ) ≤ v t ∧ ∀ a : F, (q : WithTop ℚ) ≤ v a → v t ≤ v a := by sorry
