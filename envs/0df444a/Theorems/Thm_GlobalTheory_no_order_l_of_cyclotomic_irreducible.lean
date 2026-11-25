-- Prove2me | Theorems.Thm_GlobalTheory_no_order_l_of_cyclotomic_irreducible
-- name    : GlobalTheory.no_order_l_of_cyclotomic_irreducible
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:49:07.562282+00:00
-- url     : https://prove2.me/theorems/3def5c2e-3b91-4d97-a84e-79dae6ec29ea
-- title:
--   Global Theory: no order l of cyclotomic irreducible
-- statement:
--   The Global Theory construction uses the no order l of cyclotomic irreducible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NoOrderLOfCyclotomicIrreducible.lean#L6-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NoOrderLOfCyclotomicIrreducible.lean#L6-L30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NoOrderLOfCyclotomicIrreducible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Polynomial

theorem GlobalTheory.no_order_l_of_cyclotomic_irreducible :
    ∀ (E : Type) [Field E] [CharZero E] (l N : ℕ) (g : Matrix (Fin N) (Fin N) E),
      l.Prime → Irreducible (Polynomial.cyclotomic l E) → N + 1 < l → g ^ l = 1 → g = 1 := by sorry
