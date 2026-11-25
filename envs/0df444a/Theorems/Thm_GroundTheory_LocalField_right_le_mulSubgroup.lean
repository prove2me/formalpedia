-- Prove2me | Theorems.Thm_GroundTheory_LocalField_right_le_mulSubgroup
-- name    : GroundTheory.LocalField.right_le_mulSubgroup
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T02:14:31.55981+00:00
-- url     : https://prove2.me/theorems/b2dd23c3-a20e-4d46-9d2e-2ab828f7b0c2
-- title:
--   Local Field: right le mul Subgroup
-- statement:
--   The Local Field construction uses the right le mul Subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionPrime.lean#L38-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionPrime.lean#L38-L39

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionLocal
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionPrime
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
open Module Representation
open scoped Classical
universe u
variable {G : Type u} [Group G]

theorem GroundTheory.LocalField.right_le_mulSubgroup {C P : Subgroup G} (hcomm : ∀ c ∈ C, ∀ y ∈ P, c * y = y * c) :
    P ≤ mulSubgroup C P hcomm := by sorry
