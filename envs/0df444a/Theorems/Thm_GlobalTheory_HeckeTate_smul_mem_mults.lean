-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTate_smul_mem_mults
-- name    : GlobalTheory.HeckeTate.smul_mem_mults
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:47:36.357773+00:00
-- url     : https://prove2.me/theorems/f8539739-d5ff-41d0-92a1-37aa0a9288e6
-- title:
--   Hecke Tate: smul mem mults
-- statement:
--   The Hecke Tate construction uses the smul mem mults property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/DvdMulOfIdem.lean#L99-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/DvdMulOfIdem.lean#L99-L101

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DvdMulOfIdem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HeckeTate
variable {R : Type} [CommRing R] {M M' : Type} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']

theorem GlobalTheory.HeckeTate.smul_mem_mults {N r : R} (h : N ∣ r) (x : M) : r • x ∈ mults M N := by sorry
