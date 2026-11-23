-- Prove2me | Theorems.Thm_GroundTheory_Global_SemiLocal_valued_completionMap
-- name    : GroundTheory.Global.SemiLocal.valued_completionMap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:56:06.241689+00:00
-- url     : https://prove2.me/theorems/9e91ada9-fa4b-456c-9af6-c54035b0d3ce
-- title:
--   Semi Local: valued completion Map
-- statement:
--   The Semi Local construction uses the valued completion Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/ContinuousCompletionMap.lean#L63-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/ContinuousCompletionMap.lean#L63-L91

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

theorem GroundTheory.Global.SemiLocal.valued_completionMap (x : v.adicCompletion K) :
    Valued.v (completionMap v w x) = Valued.v x ^ w.asIdeal.ramificationIdx (𝓞 K) := by sorry
