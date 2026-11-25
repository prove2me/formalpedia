-- Prove2me | Theorems.Thm_GroundTheory_Global_valued_algebraMap_adicCompletion
-- name    : GroundTheory.Global.valued_algebraMap_adicCompletion
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:56:34.758005+00:00
-- url     : https://prove2.me/theorems/56e6f5eb-fc8c-5941-a9ec-05039f4b3fda
-- title:
--   Global: valued algebra Map adic Completion
-- statement:
--   The Global construction uses the valued algebra Map adic Completion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CompletionAtPlace.lean#L103-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CompletionAtPlace.lean#L103-L108

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

theorem GroundTheory.Global.valued_algebraMap_adicCompletion [w.asIdeal.LiesOver v.asIdeal]
    (x : v.adicCompletion K) :
    Valued.v (algebraMap (v.adicCompletion K) (w.adicCompletion L) x) =
      Valued.v x ^ w.asIdeal.ramificationIdx (𝓞 K) := by sorry
