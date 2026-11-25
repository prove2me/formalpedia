-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_map_frobeniusClosure
-- name    : GroundTheory.LocalField.Abstract.map_frobeniusClosure
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:10:08.49259+00:00
-- url     : https://prove2.me/theorems/ab5c5274-3a3f-4b4b-8e9e-e31b3a64cc03
-- title:
--   Abstract: map frobenius Closure
-- statement:
--   The Abstract construction uses the map frobenius Closure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Frobenius.lean#L152-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Frobenius.lean#L152-L185

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
variable [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [TotallyDisconnectedSpace G]
omit [TotallyDisconnectedSpace G]

theorem GroundTheory.LocalField.Abstract.map_frobeniusClosure (hd : Continuous d)
    (hσ : σ ∈ Subgroup.normalizer ((L ⊓ d.ker : Subgroup G) : Set G)) {N : ℕ}
    (hdσ : d σ = Multiplicative.ofAdd (N : ℤ̂)) :
    (frobeniusClosure d L σ).map d = AddSubgroup.toSubgroup (multiples N) := by sorry
