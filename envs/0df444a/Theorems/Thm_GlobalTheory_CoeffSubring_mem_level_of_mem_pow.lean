-- Prove2me | Theorems.Thm_GlobalTheory_CoeffSubring_mem_level_of_mem_pow
-- name    : GlobalTheory.CoeffSubring.mem_level_of_mem_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:41:23.796802+00:00
-- url     : https://prove2.me/theorems/b73b8e6a-3c28-4706-88e4-f93d8e7d9360
-- title:
--   Coeff Subring: mem level of mem pow
-- statement:
--   The Coeff Subring construction uses the mem level of mem pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DvdOfForallSubMulMem.lean#L58-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DvdOfForallSubMulMem.lean#L58-L60

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

theorem GlobalTheory.CoeffSubring.mem_level_of_mem_pow {n : ℕ} {x : S} (hx : x ∈ maximalIdeal S ^ (n + 1)) :
    x ∈ level p L n := by sorry
