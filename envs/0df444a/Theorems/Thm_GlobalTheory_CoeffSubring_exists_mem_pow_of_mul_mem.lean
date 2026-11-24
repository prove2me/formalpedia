-- Prove2me | Theorems.Thm_GlobalTheory_CoeffSubring_exists_mem_pow_of_mul_mem
-- name    : GlobalTheory.CoeffSubring.exists_mem_pow_of_mul_mem
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:15:02.716685+00:00
-- url     : https://prove2.me/theorems/2d040b37-b446-42f0-bac8-9a2be34dbee2
-- title:
--   Coeff Subring: exists mem pow of mul mem
-- statement:
--   The Coeff Subring construction uses the exists mem pow of mul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DvdOfForallSubMulMem.lean#L203-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DvdOfForallSubMulMem.lean#L203-L215

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DvdOfForallSubMulMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.CoeffSubring
variable {S : Type} [CommRing S] [IsLocalRing S] (p : ℕ) (L : Set S)
variable {p L}
omit [IsLocalRing S]

theorem GlobalTheory.CoeffSubring.exists_mem_pow_of_mul_mem [IsDomain S] [IsNoetherianRing S] (I : Ideal S) {r : S}
    (hr : r ≠ 0) : ∃ c : ℕ, ∀ (n : ℕ) (x : S), r * x ∈ I ^ (n + c) → x ∈ I ^ n := by sorry
