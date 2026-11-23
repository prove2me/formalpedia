-- Prove2me | Theorems.Thm_GroundTheory_Global_natCast_ne_zero_adicCompletion
-- name    : GroundTheory.Global.natCast_ne_zero_adicCompletion
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:58:38.795502+00:00
-- url     : https://prove2.me/theorems/04f0d9d9-7126-4c2d-8d1d-b6bb3af4b63c
-- title:
--   Global: nat Cast ne zero adic Completion
-- statement:
--   The Global construction uses the nat Cast ne zero adic Completion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/LocalIndexAtPlace.lean#L75-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/LocalIndexAtPlace.lean#L75-L79

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
variable {v}

theorem GroundTheory.Global.natCast_ne_zero_adicCompletion {n : ℕ} (hn : n ≠ 0) :
    (n : v.adicCompletion K) ≠ 0 := by sorry
