-- Prove2me | Theorems.Thm_GlobalTheory_T_sum_prod_of_local_choices_bijection
-- name    : GlobalTheory.T.sum_prod_of_local_choices_bijection
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:33:17.076482+00:00
-- url     : https://prove2.me/theorems/acc91f19-a9f8-42c7-b403-30a323a9c83c
-- title:
--   T: sum prod of local choices bijection
-- statement:
--   The T construction uses the sum prod of local choices bijection property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SumProdOfLocalChoicesBijectionStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SumProdOfLocalChoicesBijectionStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SumProdOfLocalChoicesBijection
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SumProdOfLocalChoicesBijectionStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Classical
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.sum_prod_of_local_choices_bijection : ∀ {ι Q R : Type} {O : ι → Type} [CommSemiring R] [TopologicalSpace R] [∀ p, Nonempty (O p)] (s : Finset ι) (Φ : Q → ∀ p, O p) (Tq : Set Q) (U : ∀ p, Set (O p)), (∀ p ∈ s, (U p).Finite) → (∀ c ∈ Tq, ∀ c' ∈ Tq, (∀ p ∈ s, Φ c p = Φ c' p) → c = c') → (∀ c ∈ Tq, ∀ p ∈ s, Φ c p ∈ U p) → (∀ x : ∀ p, O p, (∀ p ∈ s, x p ∈ U p) → ∃ c ∈ Tq, ∀ p ∈ s, Φ c p = x p) → ∀ g : ∀ p, O p → R, Tq.Finite ∧ (∑' c : Q, if c ∈ Tq then ∏ p ∈ s, g p (Φ c p) else 0) = ∏ p ∈ s, ∑' o : O p, if o ∈ U p then g p o else 0 := by sorry
