-- Prove2me | Theorems.Thm_GlobalTheory_CoeffSubring_dvd_of_forall_sub_mul_mem
-- name    : GlobalTheory.CoeffSubring.dvd_of_forall_sub_mul_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:44:57.646221+00:00
-- url     : https://prove2.me/theorems/2bf0dc03-3f43-43cc-af53-e7ac1724535d
-- title:
--   Coeff Subring: dvd of forall sub mul mem
-- statement:
--   The Coeff Subring construction uses the dvd of forall sub mul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DvdOfForallSubMulMem.lean#L217-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DvdOfForallSubMulMem.lean#L217-L229

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

theorem GlobalTheory.CoeffSubring.dvd_of_forall_sub_mul_mem [IsNoetherianRing S] {r a : S}
    (h : ∀ n, ∃ t, a - r * t ∈ maximalIdeal S ^ n) : r ∣ a := by sorry
