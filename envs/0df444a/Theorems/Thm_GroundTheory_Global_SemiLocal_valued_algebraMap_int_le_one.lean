-- Prove2me | Theorems.Thm_GroundTheory_Global_SemiLocal_valued_algebraMap_int_le_one
-- name    : GroundTheory.Global.SemiLocal.valued_algebraMap_int_le_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:56:19.774702+00:00
-- url     : https://prove2.me/theorems/f6135f5c-2b3f-43e3-a14d-245c98ce9007
-- title:
--   Semi Local: valued algebra Map int le one
-- statement:
--   The Semi Local construction uses the valued algebra Map int le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/LocalDegree.lean#L23-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/LocalDegree.lean#L23-L26

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

theorem GroundTheory.Global.SemiLocal.valued_algebraMap_int_le_one (b : 𝓞 F) :
    Valued.v (algebraMap (𝓞 F) (u.adicCompletion F) b) ≤ 1 := by sorry
