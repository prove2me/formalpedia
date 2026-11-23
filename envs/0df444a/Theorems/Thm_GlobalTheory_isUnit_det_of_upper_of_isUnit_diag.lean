-- Prove2me | Theorems.Thm_GlobalTheory_isUnit_det_of_upper_of_isUnit_diag
-- name    : GlobalTheory.isUnit_det_of_upper_of_isUnit_diag
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:33:23.093053+00:00
-- url     : https://prove2.me/theorems/359ffada-cf1e-401f-b85c-c9f1e9d7d8e8
-- title:
--   Global Theory: is Unit det of upper of is Unit diag
-- statement:
--   The Global Theory construction uses the is Unit det of upper of is Unit diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsLowerMulUpperOfLeadingMinors.lean#L96-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsLowerMulUpperOfLeadingMinors.lean#L96-L99

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsLowerMulUpperOfLeadingMinors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Matrix
variable {R : Type} [CommRing R]

theorem GlobalTheory.isUnit_det_of_upper_of_isUnit_diag {r : ℕ} (b : Matrix (Fin r) (Fin r) R)
    (hb : b.BlockTriangular id) (hu : ∀ i, IsUnit (b i i)) : IsUnit b.det := by sorry
