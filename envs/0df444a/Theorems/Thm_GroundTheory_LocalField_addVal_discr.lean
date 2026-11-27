-- Prove2me | Theorems.Thm_GroundTheory_LocalField_addVal_discr
-- name    : GroundTheory.LocalField.addVal_discr
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:59:57.626437+00:00
-- url     : https://prove2.me/theorems/45d42b09-cddc-581a-aba4-e37366aa18bf
-- title:
--   Local Field: add Val discr
-- statement:
--   The Local Field construction uses the add Val discr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Different.lean#L306-L317
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Different.lean#L306-L317

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

theorem GroundTheory.LocalField.addVal_discr {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι 𝒪[K] 𝒪[L]) :
    IsDiscreteValuationRing.addVal 𝒪[K] (Algebra.discr 𝒪[K] b) =
      (residueDegree K L * differentExponent K L : ℕ) := by sorry
