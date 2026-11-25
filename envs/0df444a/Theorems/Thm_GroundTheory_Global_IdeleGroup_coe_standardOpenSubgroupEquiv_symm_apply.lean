-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_standardOpenSubgroupEquiv_symm_apply
-- name    : GroundTheory.Global.IdeleGroup.coe_standardOpenSubgroupEquiv_symm_apply
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:40:35.900142+00:00
-- url     : https://prove2.me/theorems/c7300884-f328-4a10-96b2-4c874f6728b5
-- title:
--   Idele Group: coe standard Open Subgroup Equiv symm apply
-- statement:
--   The Idele Group construction uses the coe standard Open Subgroup Equiv symm apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/StandardOpenEquiv.lean#L161-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/StandardOpenEquiv.lean#L161-L165

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_ClassGroup
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_StandardOpenEquiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain Topology
open scoped NumberField.AdeleRing
noncomputable section
open GroundTheory.Global.IdeleGroup
variable {K : Type*} [Field K] [NumberField K]

theorem GroundTheory.Global.IdeleGroup.coe_standardOpenSubgroupEquiv_symm_apply
    (p : (InfiniteAdeleRing K)ˣ × Π v : HeightOneSpectrum (𝓞 K), (v.adicCompletionIntegers K)ˣ) :
    (((standardOpenSubgroupEquiv K).symm p : standardOpenSubgroup K) : IdeleGroup K) =
      ofIntegerUnits p.1 p.2 := by sorry

attribute [defeq] GroundTheory.Global.IdeleGroup.coe_standardOpenSubgroupEquiv_symm_apply
