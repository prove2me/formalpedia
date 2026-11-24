-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_maxMinor_mul_right
-- name    : GroundTheory.PAdicHodge.maxMinor_mul_right
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:46:36.252111+00:00
-- url     : https://prove2.me/theorems/9fc58653-86a5-433c-860d-03479b9fe661
-- title:
--   PAdic Hodge: max Minor mul right
-- statement:
--   The PAdic Hodge construction uses the max Minor mul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/SlopeCauchyBinet.lean#L128-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/SlopeCauchyBinet.lean#L128-L132

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

theorem GroundTheory.PAdicHodge.maxMinor_mul_right (B : Matrix (Fin n) (Fin k) R) (C : Matrix (Fin k) (Fin k) R)
    (s : KSubset n k) : maxMinor (B * C) s = maxMinor B s * C.det := by sorry
