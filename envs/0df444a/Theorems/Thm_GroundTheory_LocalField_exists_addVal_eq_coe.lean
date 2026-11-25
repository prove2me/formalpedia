-- Prove2me | Theorems.Thm_GroundTheory_LocalField_exists_addVal_eq_coe
-- name    : GroundTheory.LocalField.exists_addVal_eq_coe
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:59:33.248812+00:00
-- url     : https://prove2.me/theorems/3104f27a-7278-48d2-bfff-11550e57d3cf
-- title:
--   Local Field: exists add Val eq coe
-- statement:
--   The Local Field construction uses the exists add Val eq coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Eisenstein.lean#L29-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Eisenstein.lean#L29-L32

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

theorem GroundTheory.LocalField.exists_addVal_eq_coe {x : R} (hx : x ≠ 0) : ∃ k : ℕ, addVal R x = k := by sorry
