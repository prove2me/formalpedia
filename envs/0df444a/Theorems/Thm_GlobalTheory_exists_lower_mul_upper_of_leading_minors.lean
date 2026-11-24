-- Prove2me | Theorems.Thm_GlobalTheory_exists_lower_mul_upper_of_leading_minors
-- name    : GlobalTheory.exists_lower_mul_upper_of_leading_minors
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:34:33.587483+00:00
-- url     : https://prove2.me/theorems/cb3fdcc7-62ac-4dcd-867d-0e6ba63b5502
-- title:
--   Global Theory: exists lower mul upper of leading minors
-- statement:
--   The Global Theory construction uses the exists lower mul upper of leading minors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsLowerMulUpperOfLeadingMinors.lean#L15-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsLowerMulUpperOfLeadingMinors.lean#L15-L69

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

theorem GlobalTheory.exists_lower_mul_upper_of_leading_minors (r : ℕ) (h : Matrix (Fin r) (Fin r) R)
    (hm : ∀ k (hk : k ≤ r), IsUnit (h.submatrix (Fin.castLE hk) (Fin.castLE hk)).det) :
    ∃ l b : Matrix (Fin r) (Fin r) R, (∀ i j : Fin r, i < j → l i j = 0) ∧ (∀ i, l i i = 1) ∧
      b.BlockTriangular id ∧ h = l * b := by sorry
