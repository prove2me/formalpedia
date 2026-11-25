-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_mem_zpowers_sup_iff
-- name    : GroundTheory.LocalField.Abstract.mem_zpowers_sup_iff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:10:17.413976+00:00
-- url     : https://prove2.me/theorems/50e3e591-3e71-472a-9313-f13918a11239
-- title:
--   Abstract: mem zpowers sup iff
-- statement:
--   The Abstract construction uses the mem zpowers sup iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Frobenius.lean#L51-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Frobenius.lean#L51-L60

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsEqNsmulOfProjEqZero
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Valuation
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Frobenius
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField GroundTheory.LocalField.Abstract
open ProfiniteInteger
variable {G : Type*} [Group G] {d : G →* Multiplicative ℤ̂} {L : Subgroup G} {σ : G}

theorem GroundTheory.LocalField.Abstract.mem_zpowers_sup_iff (hσ : σ ∈ Subgroup.normalizer ((L ⊓ d.ker : Subgroup G) : Set G))
    {h : G} : h ∈ Subgroup.zpowers σ ⊔ (L ⊓ d.ker) ↔ ∃ k : ℤ, ∃ j ∈ L ⊓ d.ker, h = σ ^ k * j := by sorry
