-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_det_mul_eq_sum_minors
-- name    : GroundTheory.PAdicHodge.det_mul_eq_sum_minors
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:21:15.376106+00:00
-- url     : https://prove2.me/theorems/d858d271-38f5-4d93-8633-9b469d994966
-- title:
--   PAdic Hodge: det mul eq sum minors
-- statement:
--   The PAdic Hodge construction uses the det mul eq sum minors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/SlopeCauchyBinet.lean#L28-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/SlopeCauchyBinet.lean#L28-L102

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
variable {k n : ℕ}

theorem GroundTheory.PAdicHodge.det_mul_eq_sum_minors (A : Matrix (Fin k) (Fin n) R) (B : Matrix (Fin n) (Fin k) R) :
    (A * B).det =
      ∑ s : KSubset n k, (A.submatrix id s.emb).det * (B.submatrix s.emb id).det := by sorry
