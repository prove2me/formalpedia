-- Prove2me | Theorems.Thm_GroundTheory_LocalField_eq_zero_of_forall_mem_maximalIdeal_pow
-- name    : GroundTheory.LocalField.eq_zero_of_forall_mem_maximalIdeal_pow
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:18:18.912456+00:00
-- url     : https://prove2.me/theorems/179a2725-fc1b-4d40-b9f0-c9ca2bc15fb1
-- title:
--   Local Field: eq zero of forall mem maximal Ideal pow
-- statement:
--   The Local Field construction uses the eq zero of forall mem maximal Ideal pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompletedUnramified.lean#L105-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompletedUnramified.lean#L105-L108

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

theorem GroundTheory.LocalField.eq_zero_of_forall_mem_maximalIdeal_pow {x : 𝔅} (h : ∀ n, x ∈ maximalIdeal 𝔅 ^ n) :
    x = 0 := by sorry
