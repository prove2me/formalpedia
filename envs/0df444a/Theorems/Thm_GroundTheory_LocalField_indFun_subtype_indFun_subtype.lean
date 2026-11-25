-- Prove2me | Theorems.Thm_GroundTheory_LocalField_indFun_subtype_indFun_subtype
-- name    : GroundTheory.LocalField.indFun_subtype_indFun_subtype
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:35:40.789098+00:00
-- url     : https://prove2.me/theorems/6ff3cfec-950a-4fc4-8004-484b0cbc77b0
-- title:
--   Local Field: ind Fun subtype ind Fun subtype
-- statement:
--   The Local Field construction uses the ind Fun subtype ind Fun subtype property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionClifford.lean#L156-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionClifford.lean#L156-L161

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
variable {G H H' : Type*} [Group G] [Group H] [Group H'] [Fintype G] [Fintype H] [Fintype H']

theorem GroundTheory.LocalField.indFun_subtype_indFun_subtype (T : Subgroup G) [Fintype T] (K : Subgroup T) [Fintype K]
    [Fintype (K.map T.subtype)] (ψ : K → ℂ) :
    indFun T.subtype (indFun K.subtype ψ) = indFun (K.map T.subtype).subtype
      (ψ ∘ (K.equivMapOfInjective T.subtype T.subtype_injective).symm) := by sorry
