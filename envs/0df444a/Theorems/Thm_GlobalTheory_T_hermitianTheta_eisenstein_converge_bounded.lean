-- Prove2me | Theorems.Thm_GlobalTheory_T_hermitianTheta_eisenstein_converge_bounded
-- name    : GlobalTheory.T.hermitianTheta_eisenstein_converge_bounded
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:52:30.16555+00:00
-- url     : https://prove2.me/theorems/c2076e11-b803-4151-8b8e-5ebff5773f17
-- title:
--   T: hermitian Theta eisenstein converge bounded
-- statement:
--   The T construction uses the hermitian Theta eisenstein converge bounded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/HermitianThetaEisensteinConvergeBoundedStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/HermitianThetaEisensteinConvergeBoundedStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianThetaEisensteinConvergeBounded
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianThetaEisensteinConvergeBoundedStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.hermitianTheta_eisenstein_converge_bounded : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → 4 * N < n → ∀ (R : ℕ) (δ : ℝ), 0 < R → 0 < δ → ∃ C : ℝ, ∀ φ : Matrix (Fin n) (Fin N) E → ℂ, HasLevel R φ → ∀ B : ℝ, (∀ x, ‖φ x‖ ≤ B) → ∀ Z ∈ HnGe Ψ N δ, (Summable fun U : Lag E N => ‖eisTerm Ψ U.2.choose φ Z 0 0‖) ∧ ‖thH Ψ φ Z 0 0‖ ≤ C * B ∧ ‖eis Ψ φ Z 0 0‖ ≤ C * B := by sorry
