-- Prove2me | Theorems.Thm_GroundTheory_Global_SemiLocal_valued_algebraMap_field
-- name    : GroundTheory.Global.SemiLocal.valued_algebraMap_field
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:56:01.465926+00:00
-- url     : https://prove2.me/theorems/743f5d82-ec1c-4587-a046-0a61fd5cd8b7
-- title:
--   Semi Local: valued algebra Map field
-- statement:
--   The Semi Local construction uses the valued algebra Map field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/LocalDegree.lean#L33-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/LocalDegree.lean#L33-L36

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_ContinuousCompletionMap
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_LocalDegree
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
open IsDedekindDomain NumberField WithZero
noncomputable section
open GroundTheory.Global.SemiLocal
variable {F : Type*} [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F))

theorem GroundTheory.Global.SemiLocal.valued_algebraMap_field (x : F) :
    Valued.v (algebraMap F (u.adicCompletion F) x) = u.valuation F x := by sorry
