-- Prove2me | Theorems.Thm_GroundTheory_LocalField_discr_powerBasis_eq_norm_integer
-- name    : GroundTheory.LocalField.discr_powerBasis_eq_norm_integer
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:52:00.541653+00:00
-- url     : https://prove2.me/theorems/bc5b7949-8415-4a01-88e7-b71185b8943b
-- title:
--   Local Field: discr power Basis eq norm integer
-- statement:
--   The Local Field construction uses the discr power Basis eq norm integer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Different.lean#L276-L304
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Different.lean#L276-L304

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

theorem GroundTheory.LocalField.discr_powerBasis_eq_norm_integer {x : 𝒪[L]} (hint : IsIntegral 𝒪[K] x)
    (hx : Algebra.adjoin 𝒪[K] {x} = ⊤) :
    ∃ s : ℕ, Algebra.discr 𝒪[K] (PowerBasis.ofAdjoinEqTop' hint hx).basis =
      (-1) ^ s * Algebra.norm 𝒪[K] (aeval x (derivative (minpoly 𝒪[K] x))) := by sorry
