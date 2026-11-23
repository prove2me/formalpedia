-- Prove2me | Theorems.Thm_GroundTheory_LocalField_ord_mul
-- name    : GroundTheory.LocalField.ord_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:12:27.692796+00:00
-- url     : https://prove2.me/theorems/6c2fd167-3e37-4ff5-957d-0eaf5b081339
-- title:
--   Local Field: ord mul
-- statement:
--   The Local Field construction uses the ord mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnitsBasic.lean#L151-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnitsBasic.lean#L151-L152

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

theorem GroundTheory.LocalField.ord_mul {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) : ord (x * y) = ord x + ord y := by sorry
