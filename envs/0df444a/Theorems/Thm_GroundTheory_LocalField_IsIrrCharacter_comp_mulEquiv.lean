-- Prove2me | Theorems.Thm_GroundTheory_LocalField_IsIrrCharacter_comp_mulEquiv
-- name    : GroundTheory.LocalField.IsIrrCharacter.comp_mulEquiv
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:35:39.784569+00:00
-- url     : https://prove2.me/theorems/25233126-9809-4fe4-9510-20a498c2add4
-- title:
--   Is Irr Character: comp mul Equiv
-- statement:
--   The Is Irr Character construction uses the comp mul Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionClifford.lean#L262-L274
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionClifford.lean#L262-L274

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionCharacters
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionInduced
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionClifford
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

theorem GroundTheory.LocalField.IsIrrCharacter.comp_mulEquiv {H H' : Type*} [Group H] [Group H'] {θ : H → ℂ}
    (hθ : IsIrrCharacter θ) (e : H' ≃* H) : IsIrrCharacter (θ ∘ e) := by sorry
