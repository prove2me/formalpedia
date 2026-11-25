-- Prove2me | Theorems.Thm_GroundTheory_LocalField_eq_adicCompletionAlgEquiv
-- name    : GroundTheory.LocalField.eq_adicCompletionAlgEquiv
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:14:49.872463+00:00
-- url     : https://prove2.me/theorems/c5be43ce-1393-5702-ab5d-1566f640261b
-- title:
--   Local Field: eq adic Completion Alg Equiv
-- statement:
--   The Local Field construction uses the eq adic Completion Alg Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompletedUnramified.lean#L255-L265
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompletedUnramified.lean#L255-L265

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_MaximalUnramifiedIntegers
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_UnitMulPowAdic
import Definitions.Def_GroundTheory_LocalFields_CompletedUnramified
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open IsLocalRing ValuativeRel
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
local notation "𝔅" => AdicCompletion (maximalIdeal R) R
variable {S : Type*} [CommRing S] [Algebra S R]

theorem GroundTheory.LocalField.eq_adicCompletionAlgEquiv (θ : R ≃ₐ[S] R) {τ : 𝔅 →+* 𝔅}
    (hτ : ∀ r, τ (algebraMap R 𝔅 r) = algebraMap R 𝔅 (θ r)) :
    τ = (adicCompletionAlgEquiv θ : 𝔅 →+* 𝔅) := by sorry
