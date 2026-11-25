-- Prove2me | Theorems.Thm_GlobalTheory_T_measure_invertible_integral_matrices
-- name    : GlobalTheory.T.measure_invertible_integral_matrices
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:30:10.845423+00:00
-- url     : https://prove2.me/theorems/942da109-abcb-44d1-9938-b6d0f4578c7b
-- title:
--   T: measure invertible integral matrices
-- statement:
--   The T construction uses the measure invertible integral matrices property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/MeasureInvertibleIntegralMatricesStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/MeasureInvertibleIntegralMatricesStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MeasureInvertibleIntegralMatrices
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MeasureInvertibleIntegralMatricesStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.measure_invertible_integral_matrices : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → ∀ r : ℕ, ∀ (dx : Measure (Matrix (Fin r) (Fin r) F)), dx.IsAddLeftInvariant → dx (intMat O r r) = 1 → MeasurableSet (Jset (GLint O r)) ∧ dx (Jset (GLint O r)) = ENNReal.ofReal (qE q 1 r) := by sorry
