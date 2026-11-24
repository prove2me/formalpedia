-- Prove2me | Theorems.Thm_GlobalTheory_exists_basis_matrix_of_integral_preimage
-- name    : GlobalTheory.exists_basis_matrix_of_integral_preimage
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:30:36.411693+00:00
-- url     : https://prove2.me/theorems/bd8d1990-09d7-4b0c-84f4-9f250885f9a4
-- title:
--   Global Theory: exists basis matrix of integral preimage
-- statement:
--   The Global Theory construction uses the exists basis matrix of integral preimage property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegralRowSpaceBasisExists.lean#L5-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegralRowSpaceBasisExists.lean#L5-L83

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralRowSpaceBasisExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.exists_basis_matrix_of_integral_preimage
    (O k : Type) [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Field k] [Algebra O k]
    [IsFractionRing O k] (m n : ℕ) (P : Matrix (Fin m) (Fin n) k)
    (hP : ∀ c, Matrix.vecMul c P = 0 → c = 0) :
    ∃ M : Matrix (Fin m) (Fin m) k, M.det ≠ 0 ∧ ∀ c : Fin m → k,
      (∃ a : Fin n → O, Matrix.vecMul c P = fun j => algebraMap O k (a j)) ↔
        ∃ b : Fin m → O, c = Matrix.vecMul (fun i => algebraMap O k (b i)) M := by sorry
