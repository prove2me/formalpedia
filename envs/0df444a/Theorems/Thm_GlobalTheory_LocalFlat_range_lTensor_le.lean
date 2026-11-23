-- Prove2me | Theorems.Thm_GlobalTheory_LocalFlat_range_lTensor_le
-- name    : GlobalTheory.LocalFlat.range_lTensor_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:37:11.096695+00:00
-- url     : https://prove2.me/theorems/f4bc58b1-440b-48fe-b308-f51ad1206f68
-- title:
--   Local Flat: range l Tensor le
-- statement:
--   The Local Flat construction uses the range l Tensor le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IdealEqBotOfFlatQuotientOfMapMaximalIdeal.lean#L22-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IdealEqBotOfFlatQuotientOfMapMaximalIdeal.lean#L22-L28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsMemPowSubMemPowSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct LinearMap
open GlobalTheory
universe u v w
open GlobalTheory.LocalFlat
variable {A : Type u} [CommRing A]
variable {M : Type w} [AddCommGroup M] [Module A M]

theorem GlobalTheory.LocalFlat.range_lTensor_le {F G : Type*} [AddCommGroup F] [Module A F] [AddCommGroup G] [Module A G]
    (h : G →ₗ[A] F) (N : Submodule A F) (hN : ∀ g, h g ∈ N) :
    range (h.lTensor M) ≤ range (N.subtype.lTensor M) := by sorry
