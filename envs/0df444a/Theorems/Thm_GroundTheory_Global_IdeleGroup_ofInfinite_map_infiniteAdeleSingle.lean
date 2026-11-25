-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_ofInfinite_map_infiniteAdeleSingle
-- name    : GroundTheory.Global.IdeleGroup.ofInfinite_map_infiniteAdeleSingle
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:02:22.661997+00:00
-- url     : https://prove2.me/theorems/a1780e0b-1633-4018-8b7d-7f70b03a2b7f
-- title:
--   Idele Group: of Infinite map infinite Adele Single
-- statement:
--   The Idele Group construction uses the of Infinite map infinite Adele Single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeCharRayClass.lean#L81-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeCharRayClass.lean#L81-L83

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

theorem GroundTheory.Global.IdeleGroup.ofInfinite_map_infiniteAdeleSingle (w : InfinitePlace K) (a : (w.Completion)ˣ) :
    ofInfinite (Units.map (infiniteAdeleSingle w) a) = infiniteEmbedding w a := by sorry
