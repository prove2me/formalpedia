-- Prove2me | Theorems.Thm_GroundTheory_Global_SemiLocal_valued_algebraMap_int
-- name    : GroundTheory.Global.SemiLocal.valued_algebraMap_int
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:56:03.24965+00:00
-- url     : https://prove2.me/theorems/bfc6ec6e-f737-4081-8265-936afeef5ad1
-- title:
--   Semi Local: valued algebra Map int
-- statement:
--   The Semi Local construction uses the valued algebra Map int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/LocalDegree.lean#L16-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/LocalDegree.lean#L16-L21

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

theorem GroundTheory.Global.SemiLocal.valued_algebraMap_int (b : 𝓞 F) :
    Valued.v (algebraMap (𝓞 F) (u.adicCompletion F) b) = u.intValuation b := by sorry
