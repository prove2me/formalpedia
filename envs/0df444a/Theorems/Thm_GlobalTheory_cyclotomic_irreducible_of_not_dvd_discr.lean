-- Prove2me | Theorems.Thm_GlobalTheory_cyclotomic_irreducible_of_not_dvd_discr
-- name    : GlobalTheory.cyclotomic_irreducible_of_not_dvd_discr
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:44:50.892056+00:00
-- url     : https://prove2.me/theorems/501b9233-71db-4860-afd6-d7da15c9dc01
-- title:
--   Global Theory: cyclotomic irreducible of not dvd discr
-- statement:
--   The Global Theory construction uses the cyclotomic irreducible of not dvd discr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CyclotomicIrreducibleOfNotDvdDiscr.lean#L8-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CyclotomicIrreducibleOfNotDvdDiscr.lean#L8-L14

import Mathlib
import Definitions.Def_ReciprocityTheory_Chebotarev_CyclotomicIrreducibleOfForallIsUnramifiedAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CyclotomicIrreducibleOfNotDvdDiscr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Polynomial NumberField

theorem GlobalTheory.cyclotomic_irreducible_of_not_dvd_discr :
    ∀ (E : Type) [Field E] [NumberField E] (l : ℕ), l.Prime → ¬ (l : ℤ) ∣ NumberField.discr E →
      Irreducible (Polynomial.cyclotomic l E) := by sorry
