-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_maxMinor_map
-- name    : GroundTheory.PAdicHodge.maxMinor_map
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:46:41.083109+00:00
-- url     : https://prove2.me/theorems/0bb69a8b-4ffc-4b1b-b1df-316335d4ebaa
-- title:
--   PAdic Hodge: max Minor map
-- statement:
--   The PAdic Hodge construction uses the max Minor map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/SlopeCauchyBinet.lean#L158-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/SlopeCauchyBinet.lean#L158-L162

import Mathlib
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_ExistsMaxMinorNeZeroOfLinearIndependentAlt
import Definitions.Def_GroundTheory_PAdicHodge_SlopeCauchyBinet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open Matrix Finset Equiv
variable {R : Type*} [CommRing R]
variable {m n k : ℕ}

theorem GroundTheory.PAdicHodge.maxMinor_map {S : Type*} [CommRing S] (f : R →+* S) (B : Matrix (Fin n) (Fin k) R)
    (s : KSubset n k) : maxMinor (B.map f) s = f (maxMinor B s) := by sorry
