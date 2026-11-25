-- Prove2me | Theorems.Thm_GlobalTheory_IsQuasiRegularSeq_flat_of_isMaximal
-- name    : GlobalTheory.IsQuasiRegularSeq.flat_of_isMaximal
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:56:29.618917+00:00
-- url     : https://prove2.me/theorems/dee45cbb-cec3-4839-b12e-4932bb4c6f2b
-- title:
--   Is Quasi Regular Seq: flat of is Maximal
-- statement:
--   The Is Quasi Regular Seq construction uses the flat of is Maximal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsRegularOfSupportDimQuotientAddLengthLe.lean#L107-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsRegularOfSupportDimQuotientAddLengthLe.lean#L107-L147

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

theorem GlobalTheory.IsQuasiRegularSeq.flat_of_isMaximal [IsNoetherianRing A] (B : Type*) [CommRing B]
    [IsNoetherianRing B] [Algebra A B] [Module B M] [IsScalarTower A B M] [Module.Finite B M]
    {ι : Type*} [Finite ι] {f : ι → A} (h : IsQuasiRegularSeq M f)
    (hmax : (Ideal.span (Set.range f)).IsMaximal)
    (hI : (Ideal.span (Set.range f)).map (algebraMap A B) ≤ (⊥ : Ideal B).jacobson) :
    Module.Flat A M := by sorry
