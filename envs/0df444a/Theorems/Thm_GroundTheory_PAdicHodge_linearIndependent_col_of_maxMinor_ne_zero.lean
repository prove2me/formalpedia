-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_linearIndependent_col_of_maxMinor_ne_zero
-- name    : GroundTheory.PAdicHodge.linearIndependent_col_of_maxMinor_ne_zero
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:46:43.368567+00:00
-- url     : https://prove2.me/theorems/6a5d24d9-1490-47d4-8b22-1fc2ae34f699
-- title:
--   PAdic Hodge: linear Independent col of max Minor ne zero
-- statement:
--   The PAdic Hodge construction uses the linear Independent col of max Minor ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/SlopeCauchyBinet.lean#L204-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/SlopeCauchyBinet.lean#L204-L212

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

theorem GroundTheory.PAdicHodge.linearIndependent_col_of_maxMinor_ne_zero [IsDomain R] (B : Matrix (Fin n) (Fin k) R)
    (s : KSubset n k) (hs : maxMinor B s ≠ 0) : LinearIndependent R B.col := by sorry
