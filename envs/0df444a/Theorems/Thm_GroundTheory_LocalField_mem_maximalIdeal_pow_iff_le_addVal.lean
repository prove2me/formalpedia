-- Prove2me | Theorems.Thm_GroundTheory_LocalField_mem_maximalIdeal_pow_iff_le_addVal
-- name    : GroundTheory.LocalField.mem_maximalIdeal_pow_iff_le_addVal
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:59:37.206577+00:00
-- url     : https://prove2.me/theorems/35648504-aea8-4fb8-8476-2afa93ecd4aa
-- title:
--   Local Field: mem maximal Ideal pow iff le add Val
-- statement:
--   The Local Field construction uses the mem maximal Ideal pow iff le add Val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Eisenstein.lean#L65-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Eisenstein.lean#L65-L69

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_IntermediateField
import Definitions.Def_GroundTheory_LocalFields_Eisenstein
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
open ValuativeRel Polynomial IsDiscreteValuationRing
open scoped _root_.IntermediateField
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

theorem GroundTheory.LocalField.mem_maximalIdeal_pow_iff_le_addVal (k : ℕ) (x : R) :
    x ∈ IsLocalRing.maximalIdeal R ^ k ↔ (k : ℕ∞) ≤ addVal R x := by sorry
