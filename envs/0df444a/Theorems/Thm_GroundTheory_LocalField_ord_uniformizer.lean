-- Prove2me | Theorems.Thm_GroundTheory_LocalField_ord_uniformizer
-- name    : GroundTheory.LocalField.ord_uniformizer
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:16:37.442391+00:00
-- url     : https://prove2.me/theorems/3b8769b6-9033-45b6-8a7d-34849adad399
-- title:
--   Local Field: ord uniformizer
-- statement:
--   The Local Field construction uses the ord uniformizer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnitsBasic.lean#L154-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnitsBasic.lean#L154-L155

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

theorem GroundTheory.LocalField.ord_uniformizer {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) : ord (ϖ : K) = 1 := by sorry
