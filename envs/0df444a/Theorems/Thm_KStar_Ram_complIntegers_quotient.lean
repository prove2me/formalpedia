-- Prove2me | Theorems.Thm_KStar_Ram_complIntegers_quotient
-- name    : KStar.Ram.complIntegers_quotient
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:03:45.310271+00:00
-- url     : https://prove2.me/theorems/b1bf67c2-01d8-4075-96ea-33d9bebaa601
-- title:
--   Ram: compl Integers quotient
-- statement:
--   The Ram construction uses the compl Integers quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/ClassNumberBounds/InertiaRamification/ComplDefY.lean#L63-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/ClassNumberBounds/InertiaRamification/ComplDefY.lean#L63-L100

import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_HeckeCharacterChoice_TendstoUnderCofinite
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_InertiaRamification_ComplDefY
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open KStar KStar.Ram
open NumberField IsDedekindDomain IsLocalRing
variable {E : Type*} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))

theorem KStar.Ram.complIntegers_quotient (n : ℕ) :
    (w.asIdeal ^ n).map (algebraMap (𝓞 E) (w.adicCompletionIntegers E)) =
        maximalIdeal (w.adicCompletionIntegers E) ^ n ∧
      (maximalIdeal (w.adicCompletionIntegers E) ^ n).comap
        (algebraMap (𝓞 E) (w.adicCompletionIntegers E)) = w.asIdeal ^ n ∧
      (∀ y : w.adicCompletionIntegers E, ∃ x : 𝓞 E,
        y - algebraMap (𝓞 E) _ x ∈ maximalIdeal (w.adicCompletionIntegers E) ^ n) := by sorry
