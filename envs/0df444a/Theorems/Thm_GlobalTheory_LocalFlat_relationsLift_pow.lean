-- Prove2me | Theorems.Thm_GlobalTheory_LocalFlat_relationsLift_pow
-- name    : GlobalTheory.LocalFlat.relationsLift_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:39:35.968729+00:00
-- url     : https://prove2.me/theorems/a20ffd7b-3ece-4564-ad13-ee7c228ab10f
-- title:
--   Local Flat: relations Lift pow
-- statement:
--   The Local Flat construction uses the relations Lift pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IdealEqBotOfFlatQuotientOfMapMaximalIdeal.lean#L70-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IdealEqBotOfFlatQuotientOfMapMaximalIdeal.lean#L70-L114

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

theorem GlobalTheory.LocalFlat.relationsLift_pow {π : A} (h : RelationsLift (Ideal.span {π}) M)
    (hreg : IsSMulRegular M π) (k : ℕ) : RelationsLift (Ideal.span {π} ^ k) M := by sorry
