-- Prove2me | Theorems.Thm_GroundTheory_LocalField_adjoin_eq_top_of_integer_adjoin_eq_top
-- name    : GroundTheory.LocalField.adjoin_eq_top_of_integer_adjoin_eq_top
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T07:52:19.35505+00:00
-- url     : https://prove2.me/theorems/7063a27f-2ca1-4068-aee5-187b393a24b3
-- title:
--   Local Field: adjoin eq top of integer adjoin eq top
-- statement:
--   The Local Field construction uses the adjoin eq top of integer adjoin eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Different.lean#L90-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Different.lean#L90-L126

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

theorem GroundTheory.LocalField.adjoin_eq_top_of_integer_adjoin_eq_top {x : 𝒪[L]} (hx : Algebra.adjoin 𝒪[K] {x} = ⊤) :
    Algebra.adjoin K {algebraMap 𝒪[L] L x} = ⊤ := by sorry
