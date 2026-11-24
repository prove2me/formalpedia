-- Prove2me | Theorems.Thm_GroundTheory_Global_Cyclotomic_card_quotient_under
-- name    : GroundTheory.Global.Cyclotomic.card_quotient_under
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:36:28.9098+00:00
-- url     : https://prove2.me/theorems/4e338a59-43ca-4208-a2e2-9d4ecafd943b
-- title:
--   Cyclotomic: card quotient under
-- statement:
--   The Cyclotomic construction uses the card quotient under property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/Frobenius.lean#L32-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/Frobenius.lean#L32-L34

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
omit hp [NumberField K] [P.IsPrime]

theorem GroundTheory.Global.Cyclotomic.card_quotient_under : Nat.card (ℤ ⧸ P.under ℤ) = p := by sorry
