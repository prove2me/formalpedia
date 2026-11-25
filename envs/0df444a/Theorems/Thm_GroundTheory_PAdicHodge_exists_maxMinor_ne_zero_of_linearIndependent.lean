-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_exists_maxMinor_ne_zero_of_linearIndependent
-- name    : GroundTheory.PAdicHodge.exists_maxMinor_ne_zero_of_linearIndependent
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:46:44.258621+00:00
-- url     : https://prove2.me/theorems/cb645771-7d62-4c5f-ac72-52a30a551aa7
-- title:
--   PAdic Hodge: exists max Minor ne zero of linear Independent
-- statement:
--   The PAdic Hodge construction uses the exists max Minor ne zero of linear Independent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/SlopeCauchyBinet.lean#L214-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/SlopeCauchyBinet.lean#L214-L217

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

theorem GroundTheory.PAdicHodge.exists_maxMinor_ne_zero_of_linearIndependent [IsDomain R]
    (B : Matrix (Fin n) (Fin k) R) (hB : LinearIndependent R B.col) :
    ∃ s : KSubset n k, maxMinor B s ≠ 0 := by sorry
