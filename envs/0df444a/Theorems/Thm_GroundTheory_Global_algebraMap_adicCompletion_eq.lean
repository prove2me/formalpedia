-- Prove2me | Theorems.Thm_GroundTheory_Global_algebraMap_adicCompletion_eq
-- name    : GroundTheory.Global.algebraMap_adicCompletion_eq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:41:08.711133+00:00
-- url     : https://prove2.me/theorems/4f81aaa2-c49a-4b2c-993a-39d0bcb23265
-- title:
--   Global: algebra Map adic Completion eq
-- statement:
--   The Global construction uses the algebra Map adic Completion eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CompletionAtPlace.lean#L71-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CompletionAtPlace.lean#L71-L79

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped WithZero
open GroundTheory GroundTheory.Global
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [Algebra (v.adicCompletion K) (w.adicCompletion L)]
  [ContinuousSMul (v.adicCompletion K) (w.adicCompletion L)]
  [IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)]

theorem GroundTheory.Global.algebraMap_adicCompletion_eq [w.asIdeal.LiesOver v.asIdeal] :
    algebraMap (v.adicCompletion K) (w.adicCompletion L) = adicCompletionMap v w := by sorry
