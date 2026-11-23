-- Prove2me | Theorems.Thm_GroundTheory_Global_SemiLocal_ramificationIdx_mul_inertiaDeg_le_finrank
-- name    : GroundTheory.Global.SemiLocal.ramificationIdx_mul_inertiaDeg_le_finrank
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:56:14.999854+00:00
-- url     : https://prove2.me/theorems/0b48a6be-89d0-47b2-9a7e-5933a4e3437c
-- title:
--   Semi Local: ramification Idx mul inertia Deg le finrank
-- statement:
--   The Semi Local construction uses the ramification Idx mul inertia Deg le finrank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/LocalDegree.lean#L262-L276
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/LocalDegree.lean#L262-L276

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
variable {ι : Type*} [Fintype ι]

theorem GroundTheory.Global.SemiLocal.ramificationIdx_mul_inertiaDeg_le_finrank :
    w.asIdeal.ramificationIdx (𝓞 K) * w.asIdeal.inertiaDeg (𝓞 K) ≤
      Module.finrank (v.adicCompletion K) (w.adicCompletion L) := by sorry
