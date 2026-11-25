-- Prove2me | Theorems.Thm_GlobalTheory_sup_pow_smul_top_eq_top
-- name    : GlobalTheory.sup_pow_smul_top_eq_top
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:56:12.301565+00:00
-- url     : https://prove2.me/theorems/527137de-72d5-417d-afc2-0e6deeaa1f0f
-- title:
--   Global Theory: sup pow smul top eq top
-- statement:
--   The Global Theory construction uses the sup pow smul top eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsRegularOfSupportDimQuotientAddLengthLe.lean#L27-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsRegularOfSupportDimQuotientAddLengthLe.lean#L27-L35

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

theorem GlobalTheory.sup_pow_smul_top_eq_top {I : Ideal A} {N : Submodule A M} (h : N ⊔ I • ⊤ = ⊤) (n : ℕ) :
    N ⊔ I ^ n • ⊤ = ⊤ := by sorry
