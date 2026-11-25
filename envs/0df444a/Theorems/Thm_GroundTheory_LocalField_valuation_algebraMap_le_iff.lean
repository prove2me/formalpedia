-- Prove2me | Theorems.Thm_GroundTheory_LocalField_valuation_algebraMap_le_iff
-- name    : GroundTheory.LocalField.valuation_algebraMap_le_iff
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T01:26:24.099574+00:00
-- url     : https://prove2.me/theorems/d708c3a8-f652-4615-9792-fd9074cfcb1f
-- title:
--   Local Field: valuation algebra Map le iff
-- statement:
--   The Local Field construction uses the valuation algebra Map le iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/SeparableClosureValuation.lean#L29-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/SeparableClosureValuation.lean#L29-L32

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
variable {F G : Type*} [Field F] [ValuativeRel F] [Field G] [ValuativeRel G] [Algebra F G]
  [ValuativeExtension F G]

theorem GroundTheory.LocalField.valuation_algebraMap_le_iff (x y : F) :
    valuation G (algebraMap F G x) ≤ valuation G (algebraMap F G y) ↔
      valuation F x ≤ valuation F y := by sorry
