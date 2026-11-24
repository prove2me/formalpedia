-- Prove2me | Theorems.Thm_GlobalTheory_eq_one_of_lower_unitriangular_eq_mul
-- name    : GlobalTheory.eq_one_of_lower_unitriangular_eq_mul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T22:17:48.441872+00:00
-- url     : https://prove2.me/theorems/f65a0660-f752-4b39-83ac-24a34afe21b9
-- title:
--   Global Theory: eq one of lower unitriangular eq mul
-- statement:
--   The Global Theory construction uses the eq one of lower unitriangular eq mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsLowerMulUpperOfLeadingMinors.lean#L71-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsLowerMulUpperOfLeadingMinors.lean#L71-L94

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

theorem GlobalTheory.eq_one_of_lower_unitriangular_eq_mul {r : ℕ} (l l' c : Matrix (Fin r) (Fin r) R)
    (h0 : ∀ i j : Fin r, i < j → l i j = 0) (h1 : ∀ i, l i i = 1)
    (h0' : ∀ i j : Fin r, i < j → l' i j = 0) (h1' : ∀ i, l' i i = 1)
    (hc : c.BlockTriangular id) (h : l = l' * c) : c = 1 := by sorry
