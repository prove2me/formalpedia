-- Prove2me | Theorems.Thm_GroundTheory_LocalField_span_singleton_eq_maximalIdeal_pow
-- name    : GroundTheory.LocalField.span_singleton_eq_maximalIdeal_pow
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:51:03.3131+00:00
-- url     : https://prove2.me/theorems/38b892c6-5ef5-5125-b29a-427b164997c5
-- title:
--   Local Field: span singleton eq maximal Ideal pow
-- statement:
--   The Local Field construction uses the span singleton eq maximal Ideal pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Different.lean#L22-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Different.lean#L22-L31

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

theorem GroundTheory.LocalField.span_singleton_eq_maximalIdeal_pow {a : R} (ha : a ≠ 0) {n : ℕ} (hn : addVal R a = n) :
    Ideal.span {a} = IsLocalRing.maximalIdeal R ^ n := by sorry
