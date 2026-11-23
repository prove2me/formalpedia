-- Prove2me | Theorems.Thm_GroundTheory_LocalField_ord_unit
-- name    : GroundTheory.LocalField.ord_unit
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:19:04.392552+00:00
-- url     : https://prove2.me/theorems/4426f10c-d80b-4cef-925c-c2e5ce748803
-- title:
--   Local Field: ord unit
-- statement:
--   The Local Field construction uses the ord unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnitsBasic.lean#L157-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnitsBasic.lean#L157-L158

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

theorem GroundTheory.LocalField.ord_unit (u : 𝒪[K]ˣ) : ord ((u : 𝒪[K]) : K) = 0 := by sorry
