-- Prove2me | Theorems.Thm_GroundTheory_LocalField_exists_addChar_isTrivialOn_zero_not_isTrivialOn_neg_one
-- name    : GroundTheory.LocalField.exists_addChar_isTrivialOn_zero_not_isTrivialOn_neg_one
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:23:51.05124+00:00
-- url     : https://prove2.me/theorems/8d28510a-75e5-4a2b-9bd1-02e6c27c01f9
-- title:
--   Local Field: exists add Char is Trivial On zero not is Trivial On neg one
-- statement:
--   The Local Field construction uses the exists add Char is Trivial On zero not is Trivial On neg one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierExistence.lean#L82-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierExistence.lean#L82-L96

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalFourier
import Definitions.Def_GroundTheory_LocalFields_LocalFourierExistence
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
open ValuativeRel Topology Filter
open scoped WithZero Pointwise
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem GroundTheory.LocalField.exists_addChar_isTrivialOn_zero_not_isTrivialOn_neg_one :
    ∃ ψ : AddChar K Circle, IsTrivialOn ψ 0 ∧ ¬ IsTrivialOn ψ (-1) := by sorry
