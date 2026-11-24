-- Prove2me | Theorems.Thm_GlobalTheory_ncard_primesOver_eq_finrank_of_absNorm_eq_of_not_mem_sq
-- name    : GlobalTheory.ncard_primesOver_eq_finrank_of_absNorm_eq_of_not_mem_sq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:12:19.14288+00:00
-- url     : https://prove2.me/theorems/56e16453-eb68-44c0-9bae-4d0677c355d1
-- title:
--   Global Theory: ncard primes Over eq finrank of abs Norm eq of not mem sq
-- statement:
--   The Global Theory construction uses the ncard primes Over eq finrank of abs Norm eq of not mem sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NcardPrimesOverEqFinrankOfAbsNormEqOfNotMemSq.lean#L7-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NcardPrimesOverEqFinrankOfAbsNormEqOfNotMemSq.lean#L7-L43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NcardPrimesOverEqFinrankOfAbsNormEqOfNotMemSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory

theorem GlobalTheory.ncard_primesOver_eq_finrank_of_absNorm_eq_of_not_mem_sq :
    ∀ (E : Type) [Field E] [NumberField E] (p : ℕ), p.Prime →
      (∀ P : Ideal (𝓞 E), P.IsMaximal → ((p : 𝓞 E) ∈ P) →
        Ideal.absNorm P = p ∧ (p : 𝓞 E) ∉ P ^ 2) →
      (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E)).ncard = Module.finrank ℚ E := by sorry
