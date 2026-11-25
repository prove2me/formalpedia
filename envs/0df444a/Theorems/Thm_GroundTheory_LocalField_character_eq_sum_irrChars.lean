-- Prove2me | Theorems.Thm_GroundTheory_LocalField_character_eq_sum_irrChars
-- name    : GroundTheory.LocalField.character_eq_sum_irrChars
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:24.954584+00:00
-- url     : https://prove2.me/theorems/cc540691-c76f-48b1-bcda-3404389b285c
-- title:
--   Local Field: character eq sum irr Chars
-- statement:
--   The Local Field construction uses the character eq sum irr Chars property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionCharacters.lean#L276-L279
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionCharacters.lean#L276-L279

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionCharacters
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
universe u
variable {G : Type*} [Group G] [Fintype G]

theorem GroundTheory.LocalField.character_eq_sum_irrChars {V : Type u} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) :
    ρ.character = ∑ ψ ∈ irrChars G, charInner G ρ.character ψ • ψ := by sorry
