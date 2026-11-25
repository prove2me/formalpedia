-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_ofInfinite_eq_prod
-- name    : GroundTheory.Global.IdeleGroup.ofInfinite_eq_prod
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:03:15.127806+00:00
-- url     : https://prove2.me/theorems/4478eafb-dcc4-4ae6-92b3-a4e3b42656ff
-- title:
--   Idele Group: of Infinite eq prod
-- statement:
--   The Idele Group construction uses the of Infinite eq prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeCharRayClass.lean#L92-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeCharRayClass.lean#L92-L96

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeChar
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ArchCharsUnitary
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_UnitBound
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeCharRayClass
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Topology Filter NumberField IsDedekindDomain Function Complex
open scoped NumberField.AdeleRing
open GroundTheory GroundTheory.Global
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
open GroundTheory.Global.IdeleGroup

theorem GroundTheory.Global.IdeleGroup.ofInfinite_eq_prod (x : (InfiniteAdeleRing K)ˣ) :
    ofInfinite x = ∏ w, infiniteEmbedding w (infiniteComponent w x) := by sorry
