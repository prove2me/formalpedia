-- Prove2me | Theorems.Thm_GlobalTheory_flat_of_isWeaklyRegular_of_isLocalHom
-- name    : GlobalTheory.flat_of_isWeaklyRegular_of_isLocalHom
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:56:34.924814+00:00
-- url     : https://prove2.me/theorems/a54f38ce-1fcd-4896-8ac2-6b09d54736e4
-- title:
--   Global Theory: flat of is Weakly Regular of is Local Hom
-- statement:
--   The Global Theory construction uses the flat of is Weakly Regular of is Local Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsRegularOfSupportDimQuotientAddLengthLe.lean#L159-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsRegularOfSupportDimQuotientAddLengthLe.lean#L159-L165

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

theorem GlobalTheory.flat_of_isWeaklyRegular_of_isLocalHom [IsNoetherianRing A] [IsLocalRing A] (B : Type*)
    [CommRing B] [IsNoetherianRing B] [IsLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]
    [Module B M] [IsScalarTower A B M] [Module.Finite B M]
    {xs : List A} (hxs : Ideal.ofList xs = maximalIdeal A) (h : IsWeaklyRegular M xs) :
    Module.Flat A M := by sorry
