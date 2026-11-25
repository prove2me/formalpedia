-- Prove2me | Theorems.Thm_GroundTheory_Global_extensionEmbeddingOfIsReal_realUnitsHom
-- name    : GroundTheory.Global.extensionEmbeddingOfIsReal_realUnitsHom
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:01:10.377129+00:00
-- url     : https://prove2.me/theorems/d9bb5596-8598-5588-9bba-d08f9723d85e
-- title:
--   Global: extension Embedding Of Is Real real Units Hom
-- statement:
--   The Global construction uses the extension Embedding Of Is Real real Units Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeCharRayClass.lean#L28-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeCharRayClass.lean#L28-L31

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
open NumberField.InfinitePlace.Completion
omit [NumberField K]

theorem GroundTheory.Global.extensionEmbeddingOfIsReal_realUnitsHom {w : InfinitePlace K} (hw : w.IsReal) (x : ℝˣ) :
    extensionEmbeddingOfIsReal hw ((realUnitsHom hw x : (w.Completion)ˣ) : w.Completion) = x := by sorry
