-- Prove2me | Theorems.Thm_GlobalTheory_det_eq_one_of_lower_unitriangular
-- name    : GlobalTheory.det_eq_one_of_lower_unitriangular
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:36:04.692071+00:00
-- url     : https://prove2.me/theorems/98cc9257-3462-409a-8bd7-d0582267f158
-- title:
--   Global Theory: det eq one of lower unitriangular
-- statement:
--   The Global Theory construction uses the det eq one of lower unitriangular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsLowerMulUpperOfLeadingMinors.lean#L10-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsLowerMulUpperOfLeadingMinors.lean#L10-L13

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

theorem GlobalTheory.det_eq_one_of_lower_unitriangular {r : ℕ} (l : Matrix (Fin r) (Fin r) R)
    (h0 : ∀ i j : Fin r, i < j → l i j = 0) (h1 : ∀ i, l i i = 1) : l.det = 1 := by sorry
