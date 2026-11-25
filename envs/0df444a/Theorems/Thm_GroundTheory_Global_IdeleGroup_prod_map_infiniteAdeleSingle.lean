-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_prod_map_infiniteAdeleSingle
-- name    : GroundTheory.Global.IdeleGroup.prod_map_infiniteAdeleSingle
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:04:21.423876+00:00
-- url     : https://prove2.me/theorems/ae241ed6-016a-4e6a-8c8d-34dda5b0b7cd
-- title:
--   Idele Group: prod map infinite Adele Single
-- statement:
--   The Idele Group construction uses the prod map infinite Adele Single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeCharRayClass.lean#L85-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeCharRayClass.lean#L85-L90

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

theorem GroundTheory.Global.IdeleGroup.prod_map_infiniteAdeleSingle (x : (InfiniteAdeleRing K)ˣ) :
    ∏ w, Units.map (infiniteAdeleSingle w) (infiniteComponent w x) = x := by sorry
