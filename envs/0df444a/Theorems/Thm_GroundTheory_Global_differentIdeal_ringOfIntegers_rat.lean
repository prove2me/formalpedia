-- Prove2me | Theorems.Thm_GroundTheory_Global_differentIdeal_ringOfIntegers_rat
-- name    : GroundTheory.Global.differentIdeal_ringOfIntegers_rat
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:40:53.714751+00:00
-- url     : https://prove2.me/theorems/4b1b7a93-45c7-4ad8-b5d6-27078598e75c
-- title:
--   Global: different Ideal ring Of Integers rat
-- statement:
--   The Global construction uses the different Ideal ring Of Integers rat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/RelativeDiscriminant.lean#L138-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/RelativeDiscriminant.lean#L138-L144

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_ContinuousCompletionMap
import Definitions.Def_GroundTheory_GlobalFields_Artin_RelativeDiscriminant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open IsDedekindDomain NumberField Module
open GroundTheory GroundTheory.Global
variable (M : Type*) [Field M] [NumberField M]

theorem GroundTheory.Global.differentIdeal_ringOfIntegers_rat :
    differentIdeal (𝓞 ℚ) (𝓞 M) = differentIdeal ℤ (𝓞 M) := by sorry
