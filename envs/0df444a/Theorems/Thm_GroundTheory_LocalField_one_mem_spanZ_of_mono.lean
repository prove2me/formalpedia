-- Prove2me | Theorems.Thm_GroundTheory_LocalField_one_mem_spanZ_of_mono
-- name    : GroundTheory.LocalField.one_mem_spanZ_of_mono
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:33:19.299966+00:00
-- url     : https://prove2.me/theorems/23e383a7-1f74-4cc0-9d2c-c7e4d3515c94
-- title:
--   Local Field: one mem span Z of mono
-- statement:
--   The Local Field construction uses the one mem span Z of mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionAssembly.lean#L25-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionAssembly.lean#L25-L54

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionPrime
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionAssembly
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
variable (hmono : ∀ K : Subgroup G, IsElementary K → ∀ χ : K → ℂ, IsIrrCharacter χ →
    ∃ (L : Subgroup K) (μ : L →* ℂˣ), χ = indLin L μ)
include hmono

theorem GroundTheory.LocalField.one_mem_spanZ_of_mono : (1 : G → ℂ) ∈ spanZ (IsElementary (G := G)) := by sorry
