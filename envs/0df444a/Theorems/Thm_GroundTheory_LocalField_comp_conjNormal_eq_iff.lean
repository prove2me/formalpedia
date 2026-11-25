-- Prove2me | Theorems.Thm_GroundTheory_LocalField_comp_conjNormal_eq_iff
-- name    : GroundTheory.LocalField.comp_conjNormal_eq_iff
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:30:58.12505+00:00
-- url     : https://prove2.me/theorems/a0980547-5a6b-4921-8f93-07dac5785bd4
-- title:
--   Local Field: comp conj Normal eq iff
-- statement:
--   The Local Field construction uses the comp conj Normal eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionClifford.lean#L214-L226
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionClifford.lean#L214-L226

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
variable {G : Type*} [Group G] (A : Subgroup G) [hA : A.Normal]

theorem GroundTheory.LocalField.comp_conjNormal_eq_iff (θ : A → ℂ) (g h : G) :
    θ ∘ conjNormal A h = θ ∘ conjNormal A g ↔ g⁻¹ * h ∈ inertia A θ := by sorry
