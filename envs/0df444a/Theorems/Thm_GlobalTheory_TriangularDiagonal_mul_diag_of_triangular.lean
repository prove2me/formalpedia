-- Prove2me | Theorems.Thm_GlobalTheory_TriangularDiagonal_mul_diag_of_triangular
-- name    : GlobalTheory.TriangularDiagonal.mul_diag_of_triangular
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:11:46.229643+00:00
-- url     : https://prove2.me/theorems/5c3f1bff-8aed-442d-ba18-076b4bde2d61
-- title:
--   Triangular Diagonal: mul diag of triangular
-- statement:
--   The Triangular Diagonal construction uses the mul diag of triangular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MulDiagOfTriangular.lean#L5-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MulDiagOfTriangular.lean#L5-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MulDiagOfTriangular
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TriangularDiagonal

theorem GlobalTheory.TriangularDiagonal.mul_diag_of_triangular :
    ∀ {p : ℕ} {κ : Fin p → ℤ}, Function.Injective κ → ∀ {M N : Matrix (Fin p) (Fin p) ℂ},
      (∀ (a b : Fin p), κ a < κ b → M a b = (0 : ℂ)) →
      (∀ (a b : Fin p), κ a < κ b → N a b = (0 : ℂ)) →
      ∀ (i : Fin p), (M * N) i i = M i i * N i i := by sorry
