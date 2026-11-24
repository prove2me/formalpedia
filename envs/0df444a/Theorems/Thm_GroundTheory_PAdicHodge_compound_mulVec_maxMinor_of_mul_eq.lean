-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_compound_mulVec_maxMinor_of_mul_eq
-- name    : GroundTheory.PAdicHodge.compound_mulVec_maxMinor_of_mul_eq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:46:38.054299+00:00
-- url     : https://prove2.me/theorems/c39b5647-fea4-4b9d-a5c8-451752926406
-- title:
--   PAdic Hodge: compound mul Vec max Minor of mul eq
-- statement:
--   The PAdic Hodge construction uses the compound mul Vec max Minor of mul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/SlopeCauchyBinet.lean#L170-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/SlopeCauchyBinet.lean#L170-L175

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

theorem GroundTheory.PAdicHodge.compound_mulVec_maxMinor_of_mul_eq (A : Matrix (Fin n) (Fin n) R)
    (B B' : Matrix (Fin n) (Fin k) R) (C : Matrix (Fin k) (Fin k) R) (h : A * B' = B * C) :
    compound k A *ᵥ maxMinor B' = C.det • maxMinor B := by sorry
