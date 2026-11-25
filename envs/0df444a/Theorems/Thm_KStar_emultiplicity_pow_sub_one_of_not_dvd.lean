-- Prove2me | Theorems.Thm_KStar_emultiplicity_pow_sub_one_of_not_dvd
-- name    : KStar.emultiplicity_pow_sub_one_of_not_dvd
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:52:00.924668+00:00
-- url     : https://prove2.me/theorems/469c17f2-5185-432e-9cbc-8e95524d2321
-- title:
--   KStar: emultiplicity pow sub one of not dvd
-- statement:
--   The KStar construction uses the emultiplicity pow sub one of not dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/ClassNumberBounds/TotallyRealRoots.lean#L56-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/ClassNumberBounds/TotallyRealRoots.lean#L56-L64

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_TotallyRealRoots
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open KStar
variable {R : Type*} [CommRing R] [IsDomain R]

theorem KStar.emultiplicity_pow_sub_one_of_not_dvd {p u : R} (hp : Prime p) (hu : p ∣ u - 1)
    {n : ℕ} (hn : ¬ p ∣ (n : R)) : emultiplicity p (u ^ n - 1) = emultiplicity p (u - 1) := by sorry
