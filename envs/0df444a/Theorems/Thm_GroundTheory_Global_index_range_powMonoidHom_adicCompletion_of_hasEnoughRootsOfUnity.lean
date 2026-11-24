-- Prove2me | Theorems.Thm_GroundTheory_Global_index_range_powMonoidHom_adicCompletion_of_hasEnoughRootsOfUnity
-- name    : GroundTheory.Global.index_range_powMonoidHom_adicCompletion_of_hasEnoughRootsOfUnity
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:42:02.782993+00:00
-- url     : https://prove2.me/theorems/32b3ecff-829a-4ddb-85ad-9cb999e0690b
-- title:
--   Global: index range pow Monoid Hom adic Completion of has Enough Roots Of Unity
-- statement:
--   The Global construction uses the index range pow Monoid Hom adic Completion of has Enough Roots Of Unity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/LocalIndexAtPlace.lean#L90-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/LocalIndexAtPlace.lean#L90-L95

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

theorem GroundTheory.Global.index_range_powMonoidHom_adicCompletion_of_hasEnoughRootsOfUnity {n : ℕ} [NeZero n]
    [HasEnoughRootsOfUnity (v.adicCompletion K) n] :
    ((powMonoidHom n : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range.index : ℝ) =
      n ^ 2 / ‖(n : v.adicCompletion K)‖ := by sorry
