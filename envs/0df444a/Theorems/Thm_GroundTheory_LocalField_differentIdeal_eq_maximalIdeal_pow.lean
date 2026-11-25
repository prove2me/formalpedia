-- Prove2me | Theorems.Thm_GroundTheory_LocalField_differentIdeal_eq_maximalIdeal_pow
-- name    : GroundTheory.LocalField.differentIdeal_eq_maximalIdeal_pow
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T06:06:43.259206+00:00
-- url     : https://prove2.me/theorems/2b323a23-eefe-5f9e-9d74-4a46b91cf998
-- title:
--   Local Field: different Ideal eq maximal Ideal pow
-- statement:
--   The Local Field construction uses the different Ideal eq maximal Ideal pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Different.lean#L75-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Different.lean#L75-L79

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
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L]
variable [FiniteDimensional K L]
variable [Algebra.IsSeparable K L]

theorem GroundTheory.LocalField.differentIdeal_eq_maximalIdeal_pow :
    differentIdeal 𝒪[K] 𝒪[L] = 𝓂[L] ^ differentExponent K L := by sorry
