-- Prove2me | Theorems.Thm_GroundTheory_LocalField_smul_mem_spanA_of_mem
-- name    : GroundTheory.LocalField.smul_mem_spanA_of_mem
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:33:11.269414+00:00
-- url     : https://prove2.me/theorems/cc891a53-cbe5-5be1-a504-092a5945f621
-- title:
--   Local Field: smul mem span A of mem
-- statement:
--   The Local Field construction uses the smul mem span A of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionSpan.lean#L91-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionSpan.lean#L91-L100

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

theorem GroundTheory.LocalField.smul_mem_spanA_of_mem {ζ : ℂ} {a : ℂ} (ha : a ∈ Algebra.adjoin ℤ ({ζ} : Set ℂ)) {f : G → ℂ}
    (hf : f ∈ spanA E ζ) : a • f ∈ spanA E ζ := by sorry
