-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_linearIndependent_col_iff_mulVec_eq_zero
-- name    : GroundTheory.PAdicHodge.linearIndependent_col_iff_mulVec_eq_zero
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:46:35.839246+00:00
-- url     : https://prove2.me/theorems/4240d383-4bd6-4422-8681-e2c82088273f
-- title:
--   PAdic Hodge: linear Independent col iff mul Vec eq zero
-- statement:
--   The PAdic Hodge construction uses the linear Independent col iff mul Vec eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/SlopeCauchyBinet.lean#L191-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/SlopeCauchyBinet.lean#L191-L202

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

theorem GroundTheory.PAdicHodge.linearIndependent_col_iff_mulVec_eq_zero (B : Matrix (Fin n) (Fin k) R) :
    LinearIndependent R B.col ↔ ∀ v, B *ᵥ v = 0 → v = 0 := by sorry
