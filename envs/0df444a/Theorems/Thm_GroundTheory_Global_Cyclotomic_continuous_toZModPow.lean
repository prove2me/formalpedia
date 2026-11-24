-- Prove2me | Theorems.Thm_GroundTheory_Global_Cyclotomic_continuous_toZModPow
-- name    : GroundTheory.Global.Cyclotomic.continuous_toZModPow
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:37:04.5648+00:00
-- url     : https://prove2.me/theorems/c3636cc0-77aa-48f9-98d4-87d9e9be2ea2
-- title:
--   Cyclotomic: continuous to ZMod Pow
-- statement:
--   The Cyclotomic construction uses the continuous to ZMod Pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/ProfinitePadic.lean#L30-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/ProfinitePadic.lean#L30-L31

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Character
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ContinuousToZModPow
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_ProfinitePadic
import Theorems.Thm_UpperTheory_Reformulated_B_Yde3_continuous_toZModPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open scoped GroundTheory.LocalField.Abstract
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Cyclotomic
open GroundTheory.LocalField.Abstract
variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

theorem GroundTheory.Global.Cyclotomic.continuous_toZModPow (n : ℕ) : Continuous (PadicInt.toZModPow (p := ℓ) n) := by sorry
