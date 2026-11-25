-- Prove2me | Theorems.Thm_GroundTheory_LocalField_addVal_norm_integer
-- name    : GroundTheory.LocalField.addVal_norm_integer
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T07:52:55.137204+00:00
-- url     : https://prove2.me/theorems/86cd79bc-723d-4ce4-8a7f-51fe9e927cb7
-- title:
--   Local Field: add Val norm integer
-- statement:
--   The Local Field construction uses the add Val norm integer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Different.lean#L251-L274
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Different.lean#L251-L274

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
variable {K L}
variable [Algebra.IsSeparable K L]

theorem GroundTheory.LocalField.addVal_norm_integer (y : 𝒪[L]) :
    IsDiscreteValuationRing.addVal 𝒪[K] (Algebra.norm 𝒪[K] y) =
      residueDegree K L • IsDiscreteValuationRing.addVal 𝒪[L] y := by sorry
