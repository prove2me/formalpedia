-- Prove2me | Theorems.Thm_GlobalTheory_flat_of_isCM_of_ringKrullDim_add_le
-- name    : GlobalTheory.flat_of_isCM_of_ringKrullDim_add_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:56:13.049255+00:00
-- url     : https://prove2.me/theorems/d3d5c3c4-839a-44e0-af93-a20b5f054661
-- title:
--   Global Theory: flat of is CM of ring Krull Dim add le
-- statement:
--   The Global Theory construction uses the flat of is CM of ring Krull Dim add le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsRegularOfSupportDimQuotientAddLengthLe.lean#L512-L524
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsRegularOfSupportDimQuotientAddLengthLe.lean#L512-L524

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
open ReciprocityTheory.CA
variable {R : Type*} [CommRing R]
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

theorem GlobalTheory.flat_of_isCM_of_ringKrullDim_add_le [IsRegularLocalRing A] [IsLocalRing B]
    [IsLocalHom (algebraMap A B)] (hB : IsCM B)
    (hd : ringKrullDim A + ringKrullDim (B ⧸ (maximalIdeal A).map (algebraMap A B)) ≤
      ringKrullDim B) : Module.Flat A B := by sorry
