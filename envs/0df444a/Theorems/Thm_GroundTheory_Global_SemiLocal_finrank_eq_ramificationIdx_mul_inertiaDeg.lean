-- Prove2me | Theorems.Thm_GroundTheory_Global_SemiLocal_finrank_eq_ramificationIdx_mul_inertiaDeg
-- name    : GroundTheory.Global.SemiLocal.finrank_eq_ramificationIdx_mul_inertiaDeg
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T01:12:40.079691+00:00
-- url     : https://prove2.me/theorems/120381c4-b7e7-4f9f-a727-6a03441d9200
-- title:
--   Semi Local: finrank eq ramification Idx mul inertia Deg
-- statement:
--   The Semi Local construction uses the finrank eq ramification Idx mul inertia Deg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/Finite.lean#L67-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/Finite.lean#L67-L74

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_ContinuousCompletionMap
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Approximation
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_LocalDegree
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Finite
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
open IsDedekindDomain NumberField TensorProduct Module
noncomputable section
open GroundTheory.Global.SemiLocal
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (L) (v : HeightOneSpectrum (𝓞 K))

theorem GroundTheory.Global.SemiLocal.finrank_eq_ramificationIdx_mul_inertiaDeg (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal] :
    finrank (v.adicCompletion K) (w.adicCompletion L) =
      w.asIdeal.ramificationIdx (𝓞 K) * w.asIdeal.inertiaDeg (𝓞 K) := by sorry
