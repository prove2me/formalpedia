-- Prove2me | Theorems.Thm_GroundTheory_LocalField_spanZ_mono
-- name    : GroundTheory.LocalField.spanZ_mono
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:33:13.637438+00:00
-- url     : https://prove2.me/theorems/7ed048cc-67aa-501b-9cdd-1391e6e01d33
-- title:
--   Local Field: span Z mono
-- statement:
--   The Local Field construction uses the span Z mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionSpan.lean#L88-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionSpan.lean#L88-L89

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

theorem GroundTheory.LocalField.spanZ_mono {E' : Subgroup G → Prop} (h : ∀ K, E K → E' K) : spanZ E ≤ spanZ E' := by sorry
