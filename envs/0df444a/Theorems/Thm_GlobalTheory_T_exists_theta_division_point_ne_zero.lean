-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_theta_division_point_ne_zero
-- name    : GlobalTheory.T.exists_theta_division_point_ne_zero
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T17:20:26.947846+00:00
-- url     : https://prove2.me/theorems/8e067fa9-c899-5add-afd8-37392aed2e6f
-- title:
--   T: exists theta division point ne zero
-- statement:
--   The T construction uses the exists theta division point ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsThetaDivisionPointNeZeroStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsThetaDivisionPointNeZeroStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsThetaDivisionPointNeZero
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsThetaDivisionPointNeZeroStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_theta_division_point_ne_zero : ∀ (g N : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ) (β : Fin g → ℂ) (f : (Fin g → ℂ) → ℂ), τ.IsSymm → (τ.map Complex.im).PosDef → 2 ≤ N → (∀ j, β j ≠ 0) → Differentiable ℂ f → f ≠ 0 → (∀ (i : Fin g) z, f (z + Pi.single i 1) = f z) → (∀ (j : Fin g) z, f (z + τ.mulVec (Pi.single j 1)) = β j * cexp (-(2 * Real.pi * I) * N * z j) * f z) → ∃ m n : Fin g → ℤ, f ((N : ℂ)⁻¹ • ((fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ)))) ≠ 0 := by sorry
