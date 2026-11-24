-- Prove2me | Theorems.Thm_GlobalTheory_exists_prime_dvd_sub_one_irreducible_cyclotomic
-- name    : GlobalTheory.exists_prime_dvd_sub_one_irreducible_cyclotomic
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:36:29.206529+00:00
-- url     : https://prove2.me/theorems/f827afab-c80f-4b19-82fb-550a7478cbfe
-- title:
--   Global Theory: exists prime dvd sub one irreducible cyclotomic
-- statement:
--   The Global Theory construction uses the exists prime dvd sub one irreducible cyclotomic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsPrimeDvdSubOneCyclotomicIrreducibleOver.lean#L88-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsPrimeDvdSubOneCyclotomicIrreducibleOver.lean#L88-L98

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsPrimeDvdSubOneCyclotomicIrreducibleOver
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial
open GlobalTheory

theorem GlobalTheory.exists_prime_dvd_sub_one_irreducible_cyclotomic :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), n ≠ 0 →
      ∃ m : ℕ, m.Prime ∧ n ∣ m - 1 ∧ Irreducible (cyclotomic m K) := by sorry
