-- Prove2me | Theorems.Thm_GlobalTheory_IsQuasiRegularSeq_mem_pow_smul_of_map_mem
-- name    : GlobalTheory.IsQuasiRegularSeq.mem_pow_smul_of_map_mem
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:56:20.254841+00:00
-- url     : https://prove2.me/theorems/ebf1649d-52f5-4cca-8043-cf022d26ce6b
-- title:
--   Is Quasi Regular Seq: mem pow smul of map mem
-- statement:
--   The Is Quasi Regular Seq construction uses the mem pow smul of map mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsRegularOfSupportDimQuotientAddLengthLe.lean#L14-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsRegularOfSupportDimQuotientAddLengthLe.lean#L14-L25

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_ChainConnInDim
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularIffIsQuasiRegularSeqOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsIsRegularQuotSMulTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsRegularOfSupportDimQuotientAddLengthLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open RingTheory.Sequence IsLocalRing TensorProduct
open GlobalTheory
variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]

theorem GlobalTheory.IsQuasiRegularSeq.mem_pow_smul_of_map_mem {ι : Type*} [Finite ι] {f : ι → A}
    (h : IsQuasiRegularSeq M f) {F : Type*} [AddCommGroup F] [Module A F] (g : F →ₗ[A] M)
    (hg : ∀ z, g z ∈ (Ideal.span (Set.range f) • ⊤ : Submodule A M) →
      z ∈ (Ideal.span (Set.range f) • ⊤ : Submodule A F)) (n : ℕ) (z : F)
    (hz : g z ∈ (Ideal.span (Set.range f) ^ n • ⊤ : Submodule A M)) :
    z ∈ (Ideal.span (Set.range f) ^ n • ⊤ : Submodule A F) := by sorry
