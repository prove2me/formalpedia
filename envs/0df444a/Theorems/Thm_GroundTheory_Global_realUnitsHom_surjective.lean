-- Prove2me | Theorems.Thm_GroundTheory_Global_realUnitsHom_surjective
-- name    : GroundTheory.Global.realUnitsHom_surjective
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:01:38.292876+00:00
-- url     : https://prove2.me/theorems/fefc8d2e-9598-5be4-ad88-92c3c6bb5b81
-- title:
--   Global: real Units Hom surjective
-- statement:
--   The Global construction uses the real Units Hom surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeCharRayClass.lean#L35-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeCharRayClass.lean#L35-L37

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

theorem GroundTheory.Global.realUnitsHom_surjective {w : InfinitePlace K} (hw : w.IsReal) (a : (w.Completion)ˣ) :
    realUnitsHom hw (Units.map (ringEquivRealOfIsReal hw : w.Completion →+* ℝ).toMonoidHom a) = a := by sorry
