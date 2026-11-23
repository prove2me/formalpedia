-- Prove2me | Theorems.Thm_GlobalTheory_CoeffSubring_pow_sub_pow_mem
-- name    : GlobalTheory.CoeffSubring.pow_sub_pow_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:41:23.976685+00:00
-- url     : https://prove2.me/theorems/2eef4a0f-c7fa-44f9-bc72-2ca1dabbc2cb
-- title:
--   Coeff Subring: pow sub pow mem
-- statement:
--   The Coeff Subring construction uses the pow sub pow mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DvdOfForallSubMulMem.lean#L87-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DvdOfForallSubMulMem.lean#L87-L89

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

theorem GlobalTheory.CoeffSubring.pow_sub_pow_mem (h0 : (p : S) ∈ maximalIdeal S) {x y : S} (h : x - y ∈ maximalIdeal S)
    (n : ℕ) : x ^ p ^ n - y ^ p ^ n ∈ maximalIdeal S ^ (n + 1) := by sorry
