-- Prove2me | Theorems.Thm_GroundTheory_LocalField_indFun_subtype_indLin
-- name    : GroundTheory.LocalField.indFun_subtype_indLin
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:35:19.815669+00:00
-- url     : https://prove2.me/theorems/b456706b-65ec-4aea-a1ee-482a10557abd
-- title:
--   Local Field: ind Fun subtype ind Lin
-- statement:
--   The Local Field construction uses the ind Fun subtype ind Lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionSpan.lean#L54-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionSpan.lean#L54-L61

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

theorem GroundTheory.LocalField.indFun_subtype_indLin (K : Subgroup G) (L : Subgroup K) (μ : L →* ℂˣ) :
    indFun K.subtype (indLin L μ) = indLin (L.map K.subtype)
      (μ.comp (L.equivMapOfInjective K.subtype K.subtype_injective).symm.toMonoidHom) := by sorry
