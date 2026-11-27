-- Prove2me | Theorems.Thm_GlobalTheory_exists_esymm_pow_div_mem_of_isLocalRing
-- name    : GlobalTheory.exists_esymm_pow_div_mem_of_isLocalRing
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:44:57.492385+00:00
-- url     : https://prove2.me/theorems/88970f41-6151-4d59-90cc-a5c39d0656b3
-- title:
--   Global Theory: exists esymm pow div mem of is Local Ring
-- statement:
--   The Global Theory construction uses the exists esymm pow div mem of is Local Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsEsymmPowDivMemOfIsLocalRing.lean#L5-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsEsymmPowDivMemOfIsLocalRing.lean#L5-L53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsEsymmPowDivMemOfIsLocalRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.exists_esymm_pow_div_mem_of_isLocalRing : ∀ (K : Type) [Field K] (O : Subring K) [IsLocalRing O] (A : Type) [Fintype A] (x : A → K) (D k : ℕ) (c : K), 1 ≤ D → 1 ≤ k → k ∣ D → c ≠ 0 → (Finset.univ.val.map x).esymm k ^ (D / k) = c → (∀ a, x a ^ D / c ∈ O) → ∃ a, x a ≠ 0 ∧ c / x a ^ D ∈ O := by sorry
