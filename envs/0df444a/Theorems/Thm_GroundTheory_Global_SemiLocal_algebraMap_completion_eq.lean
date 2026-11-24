-- Prove2me | Theorems.Thm_GroundTheory_Global_SemiLocal_algebraMap_completion_eq
-- name    : GroundTheory.Global.SemiLocal.algebraMap_completion_eq
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:39:34.552242+00:00
-- url     : https://prove2.me/theorems/d2ca7ede-b9d0-4437-a7cf-7c3af5503eec
-- title:
--   Semi Local: algebra Map completion eq
-- statement:
--   The Semi Local construction uses the algebra Map completion eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/ContinuousCompletionMap.lean#L96-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/ContinuousCompletionMap.lean#L96-L97

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_ContinuousCompletionMap
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
open IsDedekindDomain NumberField
noncomputable section
open GroundTheory.Global.SemiLocal
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]

theorem GroundTheory.Global.SemiLocal.algebraMap_completion_eq :
    algebraMap (v.adicCompletion K) (w.adicCompletion L) = completionMap v w := by sorry
