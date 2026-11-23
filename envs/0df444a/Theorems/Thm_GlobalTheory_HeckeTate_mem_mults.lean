-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTate_mem_mults
-- name    : GlobalTheory.HeckeTate.mem_mults
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:44:00.817364+00:00
-- url     : https://prove2.me/theorems/6e7f4b69-c44f-422e-a1f1-1060a39e01aa
-- title:
--   Hecke Tate: mem mults
-- statement:
--   The Hecke Tate construction uses the mem mults property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/DvdMulOfIdem.lean#L96-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/DvdMulOfIdem.lean#L96-L97

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

theorem GlobalTheory.HeckeTate.mem_mults {N : R} {x : M} : x ∈ mults M N ↔ ∃ y, x = N • y := by sorry
