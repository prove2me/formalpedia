-- Prove2me | Theorems.Thm_GroundTheory_LocalField_differentExponent_eq_addVal
-- name    : GroundTheory.LocalField.differentExponent_eq_addVal
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T07:51:59.694062+00:00
-- url     : https://prove2.me/theorems/782f1dbe-3b92-4589-bdfd-1d91060645aa
-- title:
--   Local Field: different Exponent eq add Val
-- statement:
--   The Local Field construction uses the different Exponent eq add Val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Different.lean#L144-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Different.lean#L144-L149

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

theorem GroundTheory.LocalField.differentExponent_eq_addVal {x : 𝒪[L]} (hx : Algebra.adjoin 𝒪[K] {x} = ⊤) :
    (differentExponent K L : ℕ∞) = IsDiscreteValuationRing.addVal 𝒪[L] (aeval x (derivative (minpoly 𝒪[K] x))) := by sorry
