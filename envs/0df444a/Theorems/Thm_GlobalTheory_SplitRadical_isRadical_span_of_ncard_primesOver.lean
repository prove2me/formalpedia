-- Prove2me | Theorems.Thm_GlobalTheory_SplitRadical_isRadical_span_of_ncard_primesOver
-- name    : GlobalTheory.SplitRadical.isRadical_span_of_ncard_primesOver
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:16:44.895999+00:00
-- url     : https://prove2.me/theorems/d1c4d612-1eac-44a4-99af-77795f9bc3d0
-- title:
--   Split Radical: is Radical span of ncard primes Over
-- statement:
--   The Split Radical construction uses the is Radical span of ncard primes Over property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IsRadicalSpanPrimeOfNcardPrimesOverEqFinrank.lean#L17-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IsRadicalSpanPrimeOfNcardPrimesOverEqFinrank.lean#L17-L61

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsRadicalSpanPrimeOfNcardPrimesOverEqFinrank
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField UniqueFactorizationMonoid
open GlobalTheory GlobalTheory.SplitRadical

theorem GlobalTheory.SplitRadical.isRadical_span_of_ncard_primesOver : ∀ (E : Type) [Field E] [NumberField E] (p : ℕ), p.Prime →
    (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E)).ncard = Module.finrank ℚ E →
    (Ideal.span {(p : 𝓞 E)}).IsRadical := by sorry
