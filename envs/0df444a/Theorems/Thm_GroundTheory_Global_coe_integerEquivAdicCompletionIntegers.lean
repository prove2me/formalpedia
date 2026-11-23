-- Prove2me | Theorems.Thm_GroundTheory_Global_coe_integerEquivAdicCompletionIntegers
-- name    : GroundTheory.Global.coe_integerEquivAdicCompletionIntegers
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:47:28.362616+00:00
-- url     : https://prove2.me/theorems/17075dd9-7cec-4d4b-9f38-b8d79470b569
-- title:
--   Global: coe integer Equiv Adic Completion Integers
-- statement:
--   The Global construction uses the coe integer Equiv Adic Completion Integers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/LocalIndexAtPlace.lean#L32-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/LocalIndexAtPlace.lean#L32-L35

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_LocalIndex
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_LocalIndexAtPlace
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
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField ValuativeRel
  GroundTheory.LocalField
variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem GroundTheory.Global.coe_integerEquivAdicCompletionIntegers (x : 𝒪[v.adicCompletion K]) :
    ((integerEquivAdicCompletionIntegers v x : v.adicCompletionIntegers K) :
      v.adicCompletion K) = x := by sorry

attribute [defeq] GroundTheory.Global.coe_integerEquivAdicCompletionIntegers
