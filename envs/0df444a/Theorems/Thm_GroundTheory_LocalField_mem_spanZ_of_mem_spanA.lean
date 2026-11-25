-- Prove2me | Theorems.Thm_GroundTheory_LocalField_mem_spanZ_of_mem_spanA
-- name    : GroundTheory.LocalField.mem_spanZ_of_mem_spanA
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:32:08.325269+00:00
-- url     : https://prove2.me/theorems/ac3c304b-fe11-41e7-8304-b35b41194bee
-- title:
--   Local Field: mem span Z of mem span A
-- statement:
--   The Local Field construction uses the mem span Z of mem span A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionSpan.lean#L219-L263
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionSpan.lean#L219-L263

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
variable {E : Subgroup G → Prop}

theorem GroundTheory.LocalField.mem_spanZ_of_mem_spanA {ζ : ℂ} (hζ : IsIntegral ℤ ζ) {f : G → ℂ} (hf : f ∈ spanA E ζ)
    (hint : ∀ ψ ∈ irrChars G, ∃ k : ℤ, charInner G f ψ = k) : f ∈ spanZ E := by sorry
