-- Prove2me | Theorems.Thm_GroundTheory_LocalField_normalizedValuation_eq_exp_ord
-- name    : GroundTheory.LocalField.normalizedValuation_eq_exp_ord
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:17:56.393425+00:00
-- url     : https://prove2.me/theorems/731d4fbb-1197-49db-ab2d-7496117bdb6e
-- title:
--   Local Field: normalized Valuation eq exp ord
-- statement:
--   The Local Field construction uses the normalized Valuation eq exp ord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnitsBasic.lean#L146-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnitsBasic.lean#L146-L149

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

theorem GroundTheory.LocalField.normalizedValuation_eq_exp_ord {x : K} (hx : x ≠ 0) :
    normalizedValuation K x = WithZero.exp (-ord x) := by sorry
