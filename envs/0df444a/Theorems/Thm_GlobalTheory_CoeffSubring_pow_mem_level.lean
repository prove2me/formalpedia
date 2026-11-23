-- Prove2me | Theorems.Thm_GlobalTheory_CoeffSubring_pow_mem_level
-- name    : GlobalTheory.CoeffSubring.pow_mem_level
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:39:46.265582+00:00
-- url     : https://prove2.me/theorems/fd4929b6-5b98-4daa-b5ae-350d01b73262
-- title:
--   Coeff Subring: pow mem level
-- statement:
--   The Coeff Subring construction uses the pow mem level property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DvdOfForallSubMulMem.lean#L52-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DvdOfForallSubMulMem.lean#L52-L53

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

theorem GlobalTheory.CoeffSubring.pow_mem_level (n : ℕ) (x : S) : x ^ p ^ n ∈ level p L n := by sorry
