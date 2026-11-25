-- Prove2me | Theorems.Thm_GroundTheory_LocalField_indLin_mem_spanZ
-- name    : GroundTheory.LocalField.indLin_mem_spanZ
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:35:39.439177+00:00
-- url     : https://prove2.me/theorems/2cf321d1-ac62-4099-a1ef-3edd5b05085a
-- title:
--   Local Field: ind Lin mem span Z
-- statement:
--   The Local Field construction uses the ind Lin mem span Z property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionSpan.lean#L78-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionSpan.lean#L78-L79

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

theorem GroundTheory.LocalField.indLin_mem_spanZ {K : Subgroup G} (hK : E K) (l : K →* ℂˣ) : indLin K l ∈ spanZ E := by sorry
