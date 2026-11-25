-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_Supernatural_ofNat_prime_dvd_iSup_iff
-- name    : GroundTheory.ProfCoh.Supernatural.ofNat_prime_dvd_iSup_iff
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:48:16.78289+00:00
-- url     : https://prove2.me/theorems/98647c69-cc4a-4001-8ec6-1dd0ac1a50a0
-- title:
--   Supernatural: of Nat prime dvd i Sup iff
-- statement:
--   The Supernatural construction uses the of Nat prime dvd i Sup iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/Supernatural.lean#L95-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/Supernatural.lean#L95-L105

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

theorem GroundTheory.ProfCoh.Supernatural.ofNat_prime_dvd_iSup_iff (p : Nat.Primes) {ι : Sort*} (f : ι → Supernatural) :
    ofNat p ∣ ⨆ i, f i ↔ ∃ i, ofNat p ∣ f i := by sorry
