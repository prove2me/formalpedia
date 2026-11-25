-- Prove2me | Theorems.Thm_GroundTheory_LocalField_smul_mem_spanA
-- name    : GroundTheory.LocalField.smul_mem_spanA
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T01:55:29.615169+00:00
-- url     : https://prove2.me/theorems/24d7dbab-3ce9-4e39-a63d-e782f0c0eebd
-- title:
--   Local Field: smul mem span A
-- statement:
--   The Local Field construction uses the smul mem span A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionSpan.lean#L84-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionSpan.lean#L84-L86

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

theorem GroundTheory.LocalField.smul_mem_spanA {ζ : ℂ} {a : ℂ} (ha : a ∈ Algebra.adjoin ℤ ({ζ} : Set ℂ)) {g : G → ℂ}
    (hg : g ∈ spanZ E) : a • g ∈ spanA E ζ := by sorry
