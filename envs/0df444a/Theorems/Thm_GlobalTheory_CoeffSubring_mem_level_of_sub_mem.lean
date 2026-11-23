-- Prove2me | Theorems.Thm_GlobalTheory_CoeffSubring_mem_level_of_sub_mem
-- name    : GlobalTheory.CoeffSubring.mem_level_of_sub_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:41:29.094568+00:00
-- url     : https://prove2.me/theorems/26161a33-8bd7-4250-9349-5a9d1b339c3e
-- title:
--   Coeff Subring: mem level of sub mem
-- statement:
--   The Coeff Subring construction uses the mem level of sub mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DvdOfForallSubMulMem.lean#L62-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DvdOfForallSubMulMem.lean#L62-L64

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

theorem GlobalTheory.CoeffSubring.mem_level_of_sub_mem {n : ℕ} {x a : S} (ha : a ∈ level p L n)
    (hx : x - a ∈ maximalIdeal S ^ (n + 1)) : x ∈ level p L n := by sorry
