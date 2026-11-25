-- Prove2me | Theorems.Thm_GroundTheory_LocalField_charInner_comp_conjNormal
-- name    : GroundTheory.LocalField.charInner_comp_conjNormal
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:35:10.482622+00:00
-- url     : https://prove2.me/theorems/7ad81b7e-976f-5774-b671-d625abcc6ad4
-- title:
--   Local Field: char Inner comp conj Normal
-- statement:
--   The Local Field construction uses the char Inner comp conj Normal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionClifford.lean#L250-L258
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionClifford.lean#L250-L258

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

theorem GroundTheory.LocalField.charInner_comp_conjNormal [Fintype A] {χ : G → ℂ} (hχ : IsClassFun χ) (θ : A → ℂ) (g : G) :
    charInner A (χ ∘ A.subtype) (θ ∘ conjNormal A g) = charInner A (χ ∘ A.subtype) θ := by sorry
