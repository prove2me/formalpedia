-- Prove2me | Theorems.Thm_GroundTheory_LocalField_normalizedValuation_le_one_iff
-- name    : GroundTheory.LocalField.normalizedValuation_le_one_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:22:44.645155+00:00
-- url     : https://prove2.me/theorems/ee755d4e-5c5e-4f6d-841c-d59257703a3e
-- title:
--   Local Field: normalized Valuation le one iff
-- statement:
--   The Local Field construction uses the normalized Valuation le one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnitsBasic.lean#L94-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnitsBasic.lean#L94-L97

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

theorem GroundTheory.LocalField.normalizedValuation_le_one_iff {x : K} :
    normalizedValuation K x ≤ 1 ↔ x ∈ 𝒪[K] := by sorry
