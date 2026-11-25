-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_isDiscreteModule_iff
-- name    : GroundTheory.LocalField.Abstract.isDiscreteModule_iff
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:43:55.486798+00:00
-- url     : https://prove2.me/theorems/314f96cc-8127-431b-a419-a84a768f1eb1
-- title:
--   Abstract: is Discrete Module iff
-- statement:
--   The Abstract construction uses the is Discrete Module iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/ExistsOpenSubgroupMemFixedModule.lean#L48-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/ExistsOpenSubgroupMemFixedModule.lean#L48-L56

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ProfiniteInteger
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsOpenSubgroupMemFixedModule
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
variable {G : Type*} [Group G] [TopologicalSpace G] {A : Type*} [CommGroup A]
  [MulDistribMulAction G A]

theorem GroundTheory.LocalField.Abstract.isDiscreteModule_iff [ContinuousMul G] :
    IsDiscreteModule G A ↔ ∀ a : A, ∃ U : OpenSubgroup G, a ∈ fixedModule A (U : Subgroup G) := by sorry
