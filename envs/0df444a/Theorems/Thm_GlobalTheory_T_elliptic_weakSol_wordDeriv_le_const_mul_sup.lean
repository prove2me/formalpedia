-- Prove2me | Theorems.Thm_GlobalTheory_T_elliptic_weakSol_wordDeriv_le_const_mul_sup
-- name    : GlobalTheory.T.elliptic_weakSol_wordDeriv_le_const_mul_sup
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:33:27.465349+00:00
-- url     : https://prove2.me/theorems/3f7f774a-1f2f-4abb-a90a-cc535fcd6dba
-- title:
--   T: elliptic weak Sol word Deriv le const mul sup
-- statement:
--   The T construction uses the elliptic weak Sol word Deriv le const mul sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EllipticWeakSolWordDerivLeConstMulSupStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EllipticWeakSolWordDerivLeConstMulSupStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EllipticWeakSolWordDerivLeConstMulSup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EllipticWeakSolWordDerivLeConstMulSupStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.elliptic_weakSol_wordDeriv_le_const_mul_sup : ∀ (d : ℕ) (ι : Type) [Fintype ι] (P : Sys d ι) (U : Set (E d)), IsOpen U → (∀ i n w, ContDiffOn ℝ ∞ (P.a i n w) U) → (∀ x ∈ U, ∀ ξ : E d, ξ ≠ 0 → ∃ i, P.symb i x ξ ≠ 0) → ∀ (w : List (Fin d)), ∀ x₀ ∈ U, ∃ C : ℝ, 0 ≤ C ∧ ∀ u : E d → ℂ, ContinuousOn u U → WeakSol P U u → ∀ M : ℝ, (∀ x ∈ U, ‖u x‖ ≤ M) → ‖dw w u x₀‖ ≤ C * M := by sorry
