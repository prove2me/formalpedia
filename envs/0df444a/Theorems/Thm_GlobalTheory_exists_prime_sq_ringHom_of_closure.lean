-- Prove2me | Theorems.Thm_GlobalTheory_exists_prime_sq_ringHom_of_closure
-- name    : GlobalTheory.exists_prime_sq_ringHom_of_closure
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:36:58.478641+00:00
-- url     : https://prove2.me/theorems/7295e1df-9fc2-44e6-9252-97edf946f9b0
-- title:
--   Global Theory: exists prime sq ring Hom of closure
-- statement:
--   The Global Theory construction uses the exists prime sq ring Hom of closure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NumberFieldToModPSquared.lean#L97-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NumberFieldToModPSquared.lean#L97-L119

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SepIntPolyRootModPrimeSqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NumberFieldToModPSquared
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Polynomial
open GlobalTheory

theorem GlobalTheory.exists_prime_sq_ringHom_of_closure : ∀ (K : Type) [Field K] [NumberField K] (S : Finset K) (n : ℕ), ∃ p : ℕ, p.Prime ∧ n < p ∧ Nonempty (Subring.closure (S : Set K) →+* ZMod (p ^ 2)) := by sorry
