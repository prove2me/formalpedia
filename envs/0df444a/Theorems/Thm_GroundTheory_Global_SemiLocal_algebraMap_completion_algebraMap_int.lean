-- Prove2me | Theorems.Thm_GroundTheory_Global_SemiLocal_algebraMap_completion_algebraMap_int
-- name    : GroundTheory.Global.SemiLocal.algebraMap_completion_algebraMap_int
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:39:50.604818+00:00
-- url     : https://prove2.me/theorems/2ce3c0e9-35b5-4b33-9303-c43554b4a51e
-- title:
--   Semi Local: algebra Map completion algebra Map int
-- statement:
--   The Semi Local construction uses the algebra Map completion algebra Map int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/LocalDegree.lean#L76-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/LocalDegree.lean#L76-L82

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

theorem GroundTheory.Global.SemiLocal.algebraMap_completion_algebraMap_int (r : 𝓞 K) :
    algebraMap (v.adicCompletion K) (w.adicCompletion L) (algebraMap (𝓞 K) _ r) =
      algebraMap (𝓞 L) (w.adicCompletion L) (algebraMap (𝓞 K) (𝓞 L) r) := by sorry
