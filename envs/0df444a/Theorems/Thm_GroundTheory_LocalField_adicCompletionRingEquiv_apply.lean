-- Prove2me | Theorems.Thm_GroundTheory_LocalField_adicCompletionRingEquiv_apply
-- name    : GroundTheory.LocalField.adicCompletionRingEquiv_apply
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:05:25.508634+00:00
-- url     : https://prove2.me/theorems/6d90d0b5-460a-496e-9554-63a4cfd4eabb
-- title:
--   Local Field: adic Completion Ring Equiv apply
-- statement:
--   The Local Field construction uses the adic Completion Ring Equiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompletedUnramified.lean#L225-L228
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompletedUnramified.lean#L225-L228

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

theorem GroundTheory.LocalField.adicCompletionRingEquiv_apply (θ : R ≃+* R) (x : 𝔅) :
    adicCompletionRingEquiv θ x =
      adicCompletionMap (θ : R →+* R) (maximalIdeal_le_comap_ringEquiv θ) x := by sorry
