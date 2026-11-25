-- Prove2me | Theorems.Thm_GroundTheory_LocalField_ord_le_ord_iff
-- name    : GroundTheory.LocalField.ord_le_ord_iff
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:33:27.719294+00:00
-- url     : https://prove2.me/theorems/8cb8f23c-bcc5-4b63-b3de-d541f0beed5c
-- title:
--   Local Field: ord le ord iff
-- statement:
--   The Local Field construction uses the ord le ord iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/SeparableClosureValuation.lean#L58-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/SeparableClosureValuation.lean#L58-L61

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_FiniteExtension
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_IntermediateField
import Definitions.Def_GroundTheory_LocalFields_SeparableClosure
import Definitions.Def_GroundTheory_LocalFields_SeparableClosureValuation
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
open ValuativeRel IsLocalRing
open scoped WithZero
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem GroundTheory.LocalField.ord_le_ord_iff {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    ord x ≤ ord y ↔ valuation K y ≤ valuation K x := by sorry
