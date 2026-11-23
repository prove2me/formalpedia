-- Prove2me | Theorems.Thm_GroundTheory_Global_SemiLocal_valued_algebraMap_completion
-- name    : GroundTheory.Global.SemiLocal.valued_algebraMap_completion
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:18:56.872804+00:00
-- url     : https://prove2.me/theorems/6a488e59-8b18-4034-93d6-bfdd0ddd3b02
-- title:
--   Semi Local: valued algebra Map completion
-- statement:
--   The Semi Local construction uses the valued algebra Map completion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/LocalDegree.lean#L84-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/LocalDegree.lean#L84-L87

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
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]

theorem GroundTheory.Global.SemiLocal.valued_algebraMap_completion (x : v.adicCompletion K) :
    Valued.v (algebraMap (v.adicCompletion K) (w.adicCompletion L) x) =
      Valued.v x ^ w.asIdeal.ramificationIdx (𝓞 K) := by sorry
