-- Prove2me | Theorems.Thm_GlobalTheory_T_integral_row_space_basis_exists
-- name    : GlobalTheory.T.integral_row_space_basis_exists
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:34:02.348795+00:00
-- url     : https://prove2.me/theorems/11a2317b-780f-5624-8e3c-2556c35c0681
-- title:
--   T: integral row space basis exists
-- statement:
--   The T construction uses the integral row space basis exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegralRowSpaceBasisExistsStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegralRowSpaceBasisExistsStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralRowSpaceBasisExists
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralRowSpaceBasisExistsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.integral_row_space_basis_exists : ∀ (O k : Type) [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Field k] [Algebra O k] [IsFractionRing O k] (m n : ℕ) (P : Matrix (Fin m) (Fin n) k), (∀ c, Matrix.vecMul c P = 0 → c = 0) → ∃ M : Matrix (Fin m) (Fin m) k, M.det ≠ 0 ∧ ∀ c : Fin m → k, (∃ a : Fin n → O, Matrix.vecMul c P = fun j => algebraMap O k (a j)) ↔ ∃ b : Fin m → O, c = Matrix.vecMul (fun i => algebraMap O k (b i)) M := by sorry
