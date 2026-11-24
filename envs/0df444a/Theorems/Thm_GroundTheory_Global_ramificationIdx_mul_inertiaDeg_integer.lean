-- Prove2me | Theorems.Thm_GroundTheory_Global_ramificationIdx_mul_inertiaDeg_integer
-- name    : GroundTheory.Global.ramificationIdx_mul_inertiaDeg_integer
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:42:57.278991+00:00
-- url     : https://prove2.me/theorems/919cc8c6-0757-48fb-b49c-a7dd1227df35
-- title:
--   Global: ramification Idx mul inertia Deg integer
-- statement:
--   The Global construction uses the ramification Idx mul inertia Deg integer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CompletionAtPlace/Integers.lean#L223-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CompletionAtPlace/Integers.lean#L223-L238

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Integers
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
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField ValuativeRel
open scoped WithZero
open GroundTheory GroundTheory.Global
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
  [Algebra (v.adicCompletion K) (w.adicCompletion L)]
  [ContinuousSMul (v.adicCompletion K) (w.adicCompletion L)]
  [IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)]

theorem GroundTheory.Global.ramificationIdx_mul_inertiaDeg_integer :
    𝓂[w.adicCompletion L].ramificationIdx 𝒪[v.adicCompletion K] *
        𝓂[w.adicCompletion L].inertiaDeg 𝒪[v.adicCompletion K] =
      Module.finrank (v.adicCompletion K) (w.adicCompletion L) := by sorry
