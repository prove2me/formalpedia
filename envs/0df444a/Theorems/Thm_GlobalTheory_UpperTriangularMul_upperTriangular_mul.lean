-- Prove2me | Theorems.Thm_GlobalTheory_UpperTriangularMul_upperTriangular_mul
-- name    : GlobalTheory.UpperTriangularMul.upperTriangular_mul
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:42:42.470505+00:00
-- url     : https://prove2.me/theorems/1a778806-6214-4513-b82d-697a8976fe5a
-- title:
--   Upper Triangular Mul: upper Triangular mul
-- statement:
--   The Upper Triangular Mul construction uses the upper Triangular mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/UpperTriangularMul.lean#L5-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/UpperTriangularMul.lean#L5-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_UpperTriangularMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UpperTriangularMul

theorem GlobalTheory.UpperTriangularMul.upperTriangular_mul :
    ∀ {n : ℕ} {R : Type} [inst : CommRing R] {M N : Matrix (Fin n) (Fin n) R},
      (∀ (a i : Fin n), i < a → M a i = (0 : R)) →
      (∀ (a i : Fin n), i < a → N a i = (0 : R)) →
      (∀ (a i : Fin n), i < a → (M * N) a i = (0 : R)) ∧
        ∀ (i : Fin n), (M * N) i i = M i i * N i i := by sorry
