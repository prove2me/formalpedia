-- Prove2me | Theorems.Thm_GroundTheory_Global_Cyclotomic_ne_bot_of_liesOver
-- name    : GroundTheory.Global.Cyclotomic.ne_bot_of_liesOver
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:37:56.672666+00:00
-- url     : https://prove2.me/theorems/42c7e115-ba2b-4f68-9aa5-e157d93a13e0
-- title:
--   Cyclotomic: ne bot of lies Over
-- statement:
--   The Cyclotomic construction uses the ne bot of lies Over property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/Frobenius.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/Frobenius.lean#L19-L21

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Frobenius
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Cyclotomic
variable {m : ℕ} [NeZero m] (p : ℕ) [hp : Fact p.Prime] (K : Type*) [Field K] [NumberField K]
  [IsCyclotomicExtension {m} ℚ K]
variable (P : Ideal (𝓞 K)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
omit [P.IsPrime]
include hp

theorem GroundTheory.Global.Cyclotomic.ne_bot_of_liesOver : P ≠ ⊥ := by sorry
