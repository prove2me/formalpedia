-- Prove2me | Theorems.Thm_GroundTheory_LocalField_indFun_comp_toMonoidHom
-- name    : GroundTheory.LocalField.indFun_comp_toMonoidHom
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:31:40.415124+00:00
-- url     : https://prove2.me/theorems/040dcdda-88e7-47aa-b952-8f96cad3c29f
-- title:
--   Local Field: ind Fun comp to Monoid Hom
-- statement:
--   The Local Field construction uses the ind Fun comp to Monoid Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionSpan.lean#L41-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionSpan.lean#L41-L52

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
variable {H H' : Type*} [Group H] [Fintype H] [Group H'] [Fintype H']

theorem GroundTheory.LocalField.indFun_comp_toMonoidHom (φ : H →* G) (e : H' ≃* H) (ψ : H → ℂ) :
    indFun (φ.comp e.toMonoidHom) (ψ ∘ e) = indFun φ ψ := by sorry
