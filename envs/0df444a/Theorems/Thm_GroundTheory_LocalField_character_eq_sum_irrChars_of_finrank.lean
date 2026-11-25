-- Prove2me | Theorems.Thm_GroundTheory_LocalField_character_eq_sum_irrChars_of_finrank
-- name    : GroundTheory.LocalField.character_eq_sum_irrChars_of_finrank
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:43:57.856535+00:00
-- url     : https://prove2.me/theorems/9c963d3d-1a6e-404e-90a6-50fc5af1d351
-- title:
--   Local Field: character eq sum irr Chars of finrank
-- statement:
--   The Local Field construction uses the character eq sum irr Chars of finrank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionCharacters.lean#L217-L274
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionCharacters.lean#L217-L274

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

theorem GroundTheory.LocalField.character_eq_sum_irrChars_of_finrank (n : ℕ) :
    ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V),
      finrank ℂ V = n → ρ.character = ∑ ψ ∈ irrChars G, charInner G ρ.character ψ • ψ := by sorry
