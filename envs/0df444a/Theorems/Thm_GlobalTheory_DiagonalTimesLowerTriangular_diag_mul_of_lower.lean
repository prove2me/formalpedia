-- Prove2me | Theorems.Thm_GlobalTheory_DiagonalTimesLowerTriangular_diag_mul_of_lower
-- name    : GlobalTheory.DiagonalTimesLowerTriangular.diag_mul_of_lower
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:49:24.304963+00:00
-- url     : https://prove2.me/theorems/15b012da-70dd-46d7-b9fa-fb3fcf0a5aab
-- title:
--   Diagonal Times Lower Triangular: diag mul of lower
-- statement:
--   The Diagonal Times Lower Triangular construction uses the diag mul of lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DiagMulOfLower.lean#L5-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DiagMulOfLower.lean#L5-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DiagMulOfLower
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DiagonalTimesLowerTriangular

theorem GlobalTheory.DiagonalTimesLowerTriangular.diag_mul_of_lower {K : Type} [CommRing K] {s : ℕ} {a b : Matrix (Fin s) (Fin s) K}
    (ha : ∀ (i j : Fin s), i < j → a i j = (0 : K))
    (hb : ∀ (i j : Fin s), i < j → b i j = (0 : K)) :
    ∀ (i : Fin s), (a * b) i i = a i i * b i i := by sorry
