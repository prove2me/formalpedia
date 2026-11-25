-- Prove2me | Theorems.Thm_GroundTheory_LocalField_indFun_comp_mulEquiv
-- name    : GroundTheory.LocalField.indFun_comp_mulEquiv
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:45:38.097481+00:00
-- url     : https://prove2.me/theorems/8df438ee-29cf-5a22-85a9-3c759123c2f7
-- title:
--   Local Field: ind Fun comp mul Equiv
-- statement:
--   The Local Field construction uses the ind Fun comp mul Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionClifford.lean#L126-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionClifford.lean#L126-L132

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

theorem GroundTheory.LocalField.indFun_comp_mulEquiv (φ : H' →* G) (e : H ≃* H') (ψ : H → ℂ) :
    indFun (φ.comp e.toMonoidHom) ψ = indFun φ (ψ ∘ e.symm) := by sorry
