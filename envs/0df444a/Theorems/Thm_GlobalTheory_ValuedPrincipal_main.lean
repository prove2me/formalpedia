-- Prove2me | Theorems.Thm_GlobalTheory_ValuedPrincipal_main
-- name    : GlobalTheory.ValuedPrincipal.main
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:10:48.810194+00:00
-- url     : https://prove2.me/theorems/30ece105-91a1-48c4-8f3f-8d37d02d0b7a
-- title:
--   Valued Principal: main
-- statement:
--   The Valued Principal construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/ExistsLeastOfDiscrete.lean#L126-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/ExistsLeastOfDiscrete.lean#L126-L138

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

theorem GlobalTheory.ValuedPrincipal.main : ∀ (F : Type) [Field F] (v : AddValuation F (WithTop ℚ)) (π : F), v π = ((1 : ℚ) : WithTop ℚ) → (IsAlgClosed F ∨ ∃ d : ℕ, 1 ≤ d ∧ ∀ x : F, x ≠ 0 → ∃ n : ℤ, v x = (((n : ℚ) / d : ℚ) : WithTop ℚ)) → ∀ q : ℚ, ∃ t : F, t ≠ 0 ∧ ((q : ℚ) : WithTop ℚ) ≤ v t ∧ ∀ a : F, ((q : ℚ) : WithTop ℚ) ≤ v a → ∃ c : F, (0 : WithTop ℚ) ≤ v c ∧ a = c * t := by sorry
