-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_Supernatural_ofNat_prime_dvd_iff
-- name    : GroundTheory.ProfCoh.Supernatural.ofNat_prime_dvd_iff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:48:08.444266+00:00
-- url     : https://prove2.me/theorems/a9ed2bc5-03ec-4e38-a562-747bdde2db8a
-- title:
--   Supernatural: of Nat prime dvd iff
-- statement:
--   The Supernatural construction uses the of Nat prime dvd iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/Supernatural.lean#L79-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/Supernatural.lean#L79-L93

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_Supernatural
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open GroundTheory.ProfCoh.Supernatural

theorem GroundTheory.ProfCoh.Supernatural.ofNat_prime_dvd_iff (p : Nat.Primes) (a : Supernatural) :
    ofNat p ∣ a ↔ 1 ≤ a.exp p := by sorry
