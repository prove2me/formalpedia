-- Prove2me | Theorems.Thm_GroundTheory_LocalField_isClassFun_of_mem_spanZ
-- name    : GroundTheory.LocalField.isClassFun_of_mem_spanZ
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T01:55:25.585341+00:00
-- url     : https://prove2.me/theorems/38ea45bc-0dc4-48d7-893a-2b692cf7766d
-- title:
--   Local Field: is Class Fun of mem span Z
-- statement:
--   The Local Field construction uses the is Class Fun of mem span Z property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionSpan.lean#L102-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionSpan.lean#L102-L109

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionIntegral
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionElementary
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionSpan
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
variable {G : Type*} [Group G] [Fintype G]
variable (E : Subgroup G → Prop)
variable {E}

theorem GroundTheory.LocalField.isClassFun_of_mem_spanZ {f : G → ℂ} (hf : f ∈ spanZ E) : IsClassFun f := by sorry
