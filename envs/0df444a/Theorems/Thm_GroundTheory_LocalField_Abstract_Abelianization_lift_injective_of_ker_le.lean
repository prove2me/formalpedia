-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_Abelianization_lift_injective_of_ker_le
-- name    : GroundTheory.LocalField.Abstract.Abelianization.lift_injective_of_ker_le
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:00:36.09473+00:00
-- url     : https://prove2.me/theorems/05dc7c73-31cf-40df-8f47-ffd11f5a18ec
-- title:
--   Abelianization: lift injective of ker le
-- statement:
--   The Abelianization construction uses the lift injective of ker le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/IsoPGroup.lean#L128-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/IsoPGroup.lean#L128-L138

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_IsoCyclic
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_FunctorialityTransfer
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_IsoPGroup
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
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]

theorem GroundTheory.LocalField.Abstract.Abelianization.lift_injective_of_ker_le {Γ T : Type*} [Group Γ] [CommGroup T] (f : Γ →* T)
    (h : f.ker ≤ commutator Γ) : Function.Injective (Abelianization.lift f) := by sorry
