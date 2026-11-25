-- Prove2me | Theorems.Thm_GroundTheory_Global_complexUnitsHom_surjective
-- name    : GroundTheory.Global.complexUnitsHom_surjective
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:02:58.362528+00:00
-- url     : https://prove2.me/theorems/8a6d7084-ca2a-4a27-b1cb-c85a2de5c50b
-- title:
--   Global: complex Units Hom surjective
-- statement:
--   The Global construction uses the complex Units Hom surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeCharRayClass.lean#L41-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeCharRayClass.lean#L41-L44

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

theorem GroundTheory.Global.complexUnitsHom_surjective {w : InfinitePlace K} (hw : w.IsComplex) (a : (w.Completion)ˣ) :
    complexUnitsHom hw
      (Units.map (ringEquivComplexOfIsComplex hw : w.Completion →+* ℂ).toMonoidHom a) = a := by sorry
