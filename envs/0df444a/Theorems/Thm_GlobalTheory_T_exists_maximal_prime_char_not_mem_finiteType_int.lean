-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_maximal_prime_char_not_mem_finiteType_int
-- name    : GlobalTheory.T.exists_maximal_prime_char_not_mem_finiteType_int
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:29:49.135086+00:00
-- url     : https://prove2.me/theorems/e83a5965-70c0-5afe-8add-4601125df7ae
-- title:
--   T: exists maximal prime char not mem finite Type int
-- statement:
--   The T construction uses the exists maximal prime char not mem finite Type int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsMaximalPrimeCharNotMemFiniteTypeIntStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsMaximalPrimeCharNotMemFiniteTypeIntStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMaximalPrimeCharNotMemFiniteTypeInt
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMaximalPrimeCharNotMemFiniteTypeIntStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_maximal_prime_char_not_mem_finiteType_int : ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra.FiniteType ℤ R] (f : R), f ≠ 0 → ∃ M : Ideal R, M.IsMaximal ∧ f ∉ M ∧ ∃ p : ℕ, p.Prime ∧ (p : R) ∈ M := by sorry
