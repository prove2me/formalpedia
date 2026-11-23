-- Prove2me | Theorems.Thm_GlobalTheory_CoeffSubring_mem_level_of_mem
-- name    : GlobalTheory.CoeffSubring.mem_level_of_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:39:44.114811+00:00
-- url     : https://prove2.me/theorems/eb89778b-f33c-4fe3-ac1e-72aa18ed245f
-- title:
--   Coeff Subring: mem level of mem
-- statement:
--   The Coeff Subring construction uses the mem level of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DvdOfForallSubMulMem.lean#L55-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DvdOfForallSubMulMem.lean#L55-L56

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

theorem GlobalTheory.CoeffSubring.mem_level_of_mem {n : ℕ} {x : S} (hx : x ∈ L) : x ∈ level p L n := by sorry
