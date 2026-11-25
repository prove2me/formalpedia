-- Prove2me | Theorems.Thm_GroundTheory_LocalField_apply_mem_adjoin_of_mem_spanA
-- name    : GroundTheory.LocalField.apply_mem_adjoin_of_mem_spanA
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:35:49.014175+00:00
-- url     : https://prove2.me/theorems/a2921267-e781-4c80-9f0e-3b927c7bbe15
-- title:
--   Local Field: apply mem adjoin of mem span A
-- statement:
--   The Local Field construction uses the apply mem adjoin of mem span A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionLocal.lean#L143-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionLocal.lean#L143-L154

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionSpan
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionLocal
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
variable {G : Type u} [Group G] [Fintype G]
variable {E : Subgroup G → Prop} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (Nat.card G))
include hζ

theorem GroundTheory.LocalField.apply_mem_adjoin_of_mem_spanA {f : G → ℂ} (hf : f ∈ spanA E ζ) (g : G) :
    f g ∈ Algebra.adjoin ℤ ({ζ} : Set ℂ) := by sorry
