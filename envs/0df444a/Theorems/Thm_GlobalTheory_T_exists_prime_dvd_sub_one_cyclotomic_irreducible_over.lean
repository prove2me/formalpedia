-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_prime_dvd_sub_one_cyclotomic_irreducible_over
-- name    : GlobalTheory.T.exists_prime_dvd_sub_one_cyclotomic_irreducible_over
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:38:36.008053+00:00
-- url     : https://prove2.me/theorems/3b7a41ce-1112-4079-8d11-76b520371a95
-- title:
--   T: exists prime dvd sub one cyclotomic irreducible over
-- statement:
--   The T construction uses the exists prime dvd sub one cyclotomic irreducible over property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsPrimeDvdSubOneCyclotomicIrreducibleOverStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsPrimeDvdSubOneCyclotomicIrreducibleOverStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsPrimeDvdSubOneCyclotomicIrreducibleOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsPrimeDvdSubOneCyclotomicIrreducibleOverStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_prime_dvd_sub_one_cyclotomic_irreducible_over : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), n ≠ 0 → ∃ m : ℕ, m.Prime ∧ n ∣ m - 1 ∧ Irreducible (cyclotomic m K) := by sorry
