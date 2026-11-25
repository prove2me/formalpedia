-- Prove2me | Theorems.Thm_GroundTheory_Global_isOpen_range_powMonoidHom_adicCompletion
-- name    : GroundTheory.Global.isOpen_range_powMonoidHom_adicCompletion
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:56:29.700317+00:00
-- url     : https://prove2.me/theorems/e86ac40a-c54f-4729-a310-4b8abfa31fb9
-- title:
--   Global: is Open range pow Monoid Hom adic Completion
-- statement:
--   The Global construction uses the is Open range pow Monoid Hom adic Completion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/LocalIndexAtPlace.lean#L97-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/LocalIndexAtPlace.lean#L97-L100

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
variable (v)

theorem GroundTheory.Global.isOpen_range_powMonoidHom_adicCompletion {n : ℕ} (hn : n ≠ 0) :
    IsOpen ((powMonoidHom n : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range :
      Set (v.adicCompletion K)ˣ) := by sorry
