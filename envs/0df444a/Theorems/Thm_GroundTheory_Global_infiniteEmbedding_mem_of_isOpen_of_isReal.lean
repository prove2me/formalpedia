-- Prove2me | Theorems.Thm_GroundTheory_Global_infiniteEmbedding_mem_of_isOpen_of_isReal
-- name    : GroundTheory.Global.infiniteEmbedding_mem_of_isOpen_of_isReal
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:22:01.611056+00:00
-- url     : https://prove2.me/theorems/c1b08f08-0607-4219-80d0-74c5ff31f575
-- title:
--   Global: infinite Embedding mem of is Open of is Real
-- statement:
--   The Global construction uses the infinite Embedding mem of is Open of is Real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ClassFieldConsequences/OpenSubgroup.lean#L32-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ClassFieldConsequences/OpenSubgroup.lean#L32-L48

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ClassFieldConsequences_CongruenceSubgroupLeStandardOpenSubgroup
import Definitions.Def_GroundTheory_GlobalFields_ClassFieldConsequences_OpenSubgroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Topology Filter NumberField IsDedekindDomain Function
open scoped NumberField.AdeleRing
open GroundTheory GroundTheory.Global
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
open IdeleGroup

theorem GroundTheory.Global.infiniteEmbedding_mem_of_isOpen_of_isReal (H : Subgroup (IdeleGroup K))
    (hH : IsOpen (H : Set (IdeleGroup K))) {w : InfinitePlace K} (hw : w.IsReal)
    {a : (w.Completion)ˣ}
    (ha : 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (a : w.Completion)) :
    infiniteEmbedding w a ∈ H := by sorry
