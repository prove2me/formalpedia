-- Prove2me | Theorems.Thm_GlobalTheory_coeffs_mem_maximalIdeal_of_sum_mem_sq
-- name    : GlobalTheory.coeffs_mem_maximalIdeal_of_sum_mem_sq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:11:12.518839+00:00
-- url     : https://prove2.me/theorems/74342180-a3f8-45ef-b0b0-2c91f9a99ff4
-- title:
--   Global Theory: coeffs mem maximal Ideal of sum mem sq
-- statement:
--   The Global Theory construction uses the coeffs mem maximal Ideal of sum mem sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsMinimalLocalGenerators.lean#L7-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsMinimalLocalGenerators.lean#L7-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMulMemOfForall
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMinimalLocalGenerators
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory

theorem GlobalTheory.coeffs_mem_maximalIdeal_of_sum_mem_sq {R : Type} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] {n : ℕ} (z : Fin n → R) (hz : Ideal.span (Set.range z) = maximalIdeal R)
    (hn : n = (maximalIdeal R).spanFinrank) (b : Fin n → R)
    (hb : ∑ j, b j * z j ∈ maximalIdeal R ^ 2) : ∀ j, b j ∈ maximalIdeal R := by sorry
