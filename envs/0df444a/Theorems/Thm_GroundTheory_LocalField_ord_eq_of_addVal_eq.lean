-- Prove2me | Theorems.Thm_GroundTheory_LocalField_ord_eq_of_addVal_eq
-- name    : GroundTheory.LocalField.ord_eq_of_addVal_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:50:31.498346+00:00
-- url     : https://prove2.me/theorems/f49efa0a-a477-5240-909f-7fbbbe080e9c
-- title:
--   Local Field: ord eq of add Val eq
-- statement:
--   The Local Field construction uses the ord eq of add Val eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Different.lean#L230-L247
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Different.lean#L230-L247

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

theorem GroundTheory.LocalField.ord_eq_of_addVal_eq {a : 𝒪[K]} (ha : a ≠ 0) {n : ℕ}
    (hn : IsDiscreteValuationRing.addVal 𝒪[K] a = n) : ord (a : K) = n := by sorry
