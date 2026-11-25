-- Prove2me | Theorems.Thm_GroundTheory_Global_card_primesOver_le_finrank
-- name    : GroundTheory.Global.card_primesOver_le_finrank
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:40:42.385782+00:00
-- url     : https://prove2.me/theorems/baf0c291-bffa-4f0a-ac8f-5d11432ba3ec
-- title:
--   Global: card primes Over le finrank
-- statement:
--   The Global construction uses the card primes Over le finrank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/DegreeOnePrimes.lean#L9-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/DegreeOnePrimes.lean#L9-L19

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOnePrimes
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
open NumberField IsDedekindDomain Filter Topology Set
noncomputable section

theorem GroundTheory.Global.card_primesOver_le_finrank {R S : Type*} [CommRing R] [IsDomain R] [CommRing S]
    [Algebra R S] [Module.Finite R S] [Module.Flat R S] (p : Ideal R) [p.IsPrime]
    [Finite (p.primesOver S)] :
    Nat.card (p.primesOver S) ≤ Module.finrank R S := by sorry
