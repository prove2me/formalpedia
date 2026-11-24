-- Prove2me | Theorems.Thm_GlobalTheory_mem_map_ker_of_one_tmul_eq_zero_of_flat
-- name    : GlobalTheory.mem_map_ker_of_one_tmul_eq_zero_of_flat
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:11:24.065962+00:00
-- url     : https://prove2.me/theorems/4b1288ef-c9f8-48d6-925f-548acbfda04f
-- title:
--   Global Theory: mem map ker of one tmul eq zero of flat
-- statement:
--   The Global Theory construction uses the mem map ker of one tmul eq zero of flat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/MemMapKerOfOneTmulEqZeroOfFlat.lean#L7-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/MemMapKerOfOneTmulEqZeroOfFlat.lean#L7-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MemMapKerOfOneTmulEqZeroOfFlat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory

theorem GlobalTheory.mem_map_ker_of_one_tmul_eq_zero_of_flat (B C k : Type) [CommRing B] [CommRing C]
    [Algebra B C] [Module.Flat B C] [Field k] [Algebra B k] (c : C)
    (h : (1 : k) ⊗ₜ[B] c = 0) :
    c ∈ (RingHom.ker (algebraMap B k)).map (algebraMap B C) := by sorry
