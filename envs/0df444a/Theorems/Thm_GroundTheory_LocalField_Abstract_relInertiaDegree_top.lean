-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_relInertiaDegree_top
-- name    : GroundTheory.LocalField.Abstract.relInertiaDegree_top
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:03:30.439861+00:00
-- url     : https://prove2.me/theorems/f6e938bf-4e45-469d-924d-19ccac6fa603
-- title:
--   Abstract: rel Inertia Degree top
-- statement:
--   The Abstract construction uses the rel Inertia Degree top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Valuation.lean#L31-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Valuation.lean#L31-L34

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsOpenSubgroupMemFixedModule
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsEqNsmulOfProjEqZero
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_UniqueQuotientSubgroupOfSelf
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_RelIndexSup
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Valuation
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
variable {G : Type*} [Group G]
variable (d : G →* Multiplicative ℤ̂)
variable {d}

theorem GroundTheory.LocalField.Abstract.relInertiaDegree_top (hd : Function.Surjective d) (K : Subgroup G) :
    relInertiaDegree d ⊤ K = inertiaDegree d K := by sorry
