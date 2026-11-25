-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_eq
-- name    : GroundTheory.Global.IdeleGroup.infiniteProj_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:40:21.98237+00:00
-- url     : https://prove2.me/theorems/e750ccb2-954f-4949-8a52-988b75b331fb
-- title:
--   Idele Group: infinite Proj eq
-- statement:
--   The Idele Group construction uses the infinite Proj eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/IdeleBasis.lean#L102-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/IdeleBasis.lean#L102-L104

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_InfiniteProjInfiniteEmbeddingOfNe
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_Restricted
import Definitions.Def_GroundTheory_GlobalFields_Adele_Topology
import Definitions.Def_GroundTheory_GlobalFields_Adele_IdeleBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology TopologicalSpace NumberField IsDedekindDomain
open scoped RestrictedProduct NumberField.AdeleRing
open GroundTheory GroundTheory.Global
open GroundTheory.Global.IdeleGroup
variable (K : Type*) [Field K] [NumberField K]

theorem GroundTheory.Global.IdeleGroup.infiniteProj_eq (w : InfinitePlace K) (x : IdeleGroup K) :
    infiniteProj w x = ContinuousMulEquiv.piUnits (prodRestrictedEquiv K x).1 w := by sorry
