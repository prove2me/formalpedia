-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_maxMinor_ne_zero_iff_linearIndependent
-- name    : GroundTheory.PAdicHodge.maxMinor_ne_zero_iff_linearIndependent
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:01:23.210736+00:00
-- url     : https://prove2.me/theorems/14808c21-9ae4-5b6e-8654-bc5d2e305299
-- title:
--   PAdic Hodge: max Minor ne zero iff linear Independent
-- statement:
--   The PAdic Hodge construction uses the max Minor ne zero iff linear Independent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/SlopeCauchyBinet.lean#L225-L228
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/SlopeCauchyBinet.lean#L225-L228

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
variable {n k : ℕ}

theorem GroundTheory.PAdicHodge.maxMinor_ne_zero_iff_linearIndependent [IsDomain R] (B : Matrix (Fin n) (Fin k) R) :
    maxMinor B ≠ 0 ↔ LinearIndependent R B.col := by sorry
