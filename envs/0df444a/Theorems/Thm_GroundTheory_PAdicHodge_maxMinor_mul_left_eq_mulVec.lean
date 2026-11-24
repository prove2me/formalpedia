-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_maxMinor_mul_left_eq_mulVec
-- name    : GroundTheory.PAdicHodge.maxMinor_mul_left_eq_mulVec
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:46:37.743932+00:00
-- url     : https://prove2.me/theorems/5d6f473d-04ee-4620-975a-ac205654aea0
-- title:
--   PAdic Hodge: max Minor mul left eq mul Vec
-- statement:
--   The PAdic Hodge construction uses the max Minor mul left eq mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/SlopeCauchyBinet.lean#L143-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/SlopeCauchyBinet.lean#L143-L147

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

theorem GroundTheory.PAdicHodge.maxMinor_mul_left_eq_mulVec (P : Matrix (Fin m) (Fin n) R) (B : Matrix (Fin n) (Fin k) R) :
    maxMinor (P * B) = compound k P *ᵥ maxMinor B := by sorry
