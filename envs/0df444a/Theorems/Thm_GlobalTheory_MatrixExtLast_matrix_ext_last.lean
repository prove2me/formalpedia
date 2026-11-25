-- Prove2me | Theorems.Thm_GlobalTheory_MatrixExtLast_matrix_ext_last
-- name    : GlobalTheory.MatrixExtLast.matrix_ext_last
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:42:52.645113+00:00
-- url     : https://prove2.me/theorems/f85e51de-e72b-4c23-8dff-e82ade5768d5
-- title:
--   Matrix Ext Last: matrix ext last
-- statement:
--   The Matrix Ext Last construction uses the matrix ext last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MatrixExtLast.lean#L5-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MatrixExtLast.lean#L5-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MatrixExtLast
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.MatrixExtLast

theorem GlobalTheory.MatrixExtLast.matrix_ext_last {k : ℕ} {M N : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    (h₁ : ∀ i j : Fin k, M (Fin.castSucc i) (Fin.castSucc j) = N (Fin.castSucc i) (Fin.castSucc j))
    (h₂ : ∀ i : Fin k, M (Fin.castSucc i) (Fin.last k) = N (Fin.castSucc i) (Fin.last k))
    (h₃ : ∀ j : Fin k, M (Fin.last k) (Fin.castSucc j) = N (Fin.last k) (Fin.castSucc j))
    (h₄ : M (Fin.last k) (Fin.last k) = N (Fin.last k) (Fin.last k)) : M = N := by sorry
