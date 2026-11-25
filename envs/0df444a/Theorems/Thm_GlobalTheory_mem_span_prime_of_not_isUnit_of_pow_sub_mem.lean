-- Prove2me | Theorems.Thm_GlobalTheory_mem_span_prime_of_not_isUnit_of_pow_sub_mem
-- name    : GlobalTheory.mem_span_prime_of_not_isUnit_of_pow_sub_mem
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:54:28.166788+00:00
-- url     : https://prove2.me/theorems/0d543c0e-0ea6-4728-b44f-9efcacf691bf
-- title:
--   Global Theory: mem span prime of not is Unit of pow sub mem
-- statement:
--   The Global Theory construction uses the mem span prime of not is Unit of pow sub mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/HomValueCongruentIntModPrime.lean#L5-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/HomValueCongruentIntModPrime.lean#L5-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_HomValueCongruentIntModPrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.mem_span_prime_of_not_isUnit_of_pow_sub_mem {O : Type} [CommRing O] [IsLocalRing O] (g : ℕ)
    (hg : g.Prime) (y : O) (hy : y ^ g - y ∈ Ideal.span {(g : O)}) (hn : ¬ IsUnit y) :
    y ∈ Ideal.span {(g : O)} := by sorry
