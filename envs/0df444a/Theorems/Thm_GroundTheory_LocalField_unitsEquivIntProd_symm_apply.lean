-- Prove2me | Theorems.Thm_GroundTheory_LocalField_unitsEquivIntProd_symm_apply
-- name    : GroundTheory.LocalField.unitsEquivIntProd_symm_apply
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:08:57.776495+00:00
-- url     : https://prove2.me/theorems/965c7112-770d-489c-97ed-6ef67e5c36e3
-- title:
--   Local Field: units Equiv Int Prod symm apply
-- statement:
--   The Local Field construction uses the units Equiv Int Prod symm apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnitsBasic.lean#L244-L246
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnitsBasic.lean#L244-L246

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open ValuativeRel IsLocalRing
open scoped WithZero
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {K}

theorem GroundTheory.LocalField.unitsEquivIntProd_symm_apply {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ)
    (p : Multiplicative ℤ × 𝒪[K]ˣ) :
    (unitsEquivIntProd hϖ).symm p = unitsOfIntProd hϖ p := by sorry
