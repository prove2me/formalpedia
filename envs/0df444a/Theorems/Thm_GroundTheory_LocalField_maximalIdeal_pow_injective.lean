-- Prove2me | Theorems.Thm_GroundTheory_LocalField_maximalIdeal_pow_injective
-- name    : GroundTheory.LocalField.maximalIdeal_pow_injective
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:50:26.117339+00:00
-- url     : https://prove2.me/theorems/443f16f3-54fb-5141-8c6f-3247e9835807
-- title:
--   Local Field: maximal Ideal pow injective
-- statement:
--   The Local Field construction uses the maximal Ideal pow injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Different.lean#L40-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Different.lean#L40-L44

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Monogenic
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
import Definitions.Def_GroundTheory_LocalFields_Unramified
import Definitions.Def_GroundTheory_LocalFields_Different
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
open ValuativeRel Polynomial
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
attribute [local instance high] FaithfulSMul.to_isTorsionFree
open IsDiscreteValuationRing
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

theorem GroundTheory.LocalField.maximalIdeal_pow_injective :
    Function.Injective (fun n : ℕ ↦ IsLocalRing.maximalIdeal R ^ n) := by sorry
