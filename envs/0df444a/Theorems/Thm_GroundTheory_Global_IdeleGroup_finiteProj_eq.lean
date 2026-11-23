-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_eq
-- name    : GroundTheory.Global.IdeleGroup.finiteProj_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:26:58.139423+00:00
-- url     : https://prove2.me/theorems/1978a31a-136e-46dc-be07-88c2801b2008
-- title:
--   Idele Group: finite Proj eq
-- statement:
--   The Idele Group construction uses the finite Proj eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/IdeleBasis.lean#L98-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/IdeleBasis.lean#L98-L100

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

theorem GroundTheory.Global.IdeleGroup.finiteProj_eq (v : HeightOneSpectrum (𝓞 K)) (x : IdeleGroup K) :
    finiteProj v x = (prodRestrictedEquiv K x).2 v := by sorry
