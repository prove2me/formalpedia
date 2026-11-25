-- Prove2me | Theorems.Thm_GlobalTheory_Nef_hankelInt_sumLemma
-- name    : GlobalTheory.Nef.hankelInt_sumLemma
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:01:59.876803+00:00
-- url     : https://prove2.me/theorems/7292d6f2-54d6-49aa-87a7-f650cd28a176
-- title:
--   Nef: hankel Int sum Lemma
-- statement:
--   The Nef construction uses the hankel Int sum Lemma property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HankelDeterminantIntegralOfQuotient.lean#L11-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HankelDeterminantIntegralOfQuotient.lean#L11-L28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HankelDeterminantIntegralOfQuotient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
open GlobalTheory GlobalTheory.Nef
open PowerSeries Finset

theorem GlobalTheory.Nef.hankelInt_sumLemma {F : Type} [Field F] (E Q : PowerSeries F) (n : ℕ) (i : Fin (n + 1)) (s : ℕ) :
    ∑ l : Fin (n + 1), (if (l : ℕ) ≤ i then coeff ((i : ℕ) - l) E else 0) * coeff ((l : ℕ) + s) Q =
      coeff ((i : ℕ) + s) ((trunc ((i : ℕ) + 1) E : PowerSeries F) * Q) := by sorry
