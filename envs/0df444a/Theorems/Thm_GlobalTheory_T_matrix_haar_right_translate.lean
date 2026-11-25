-- Prove2me | Theorems.Thm_GlobalTheory_T_matrix_haar_right_translate
-- name    : GlobalTheory.T.matrix_haar_right_translate
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:10:57.041571+00:00
-- url     : https://prove2.me/theorems/9f2e7465-4518-43fe-818b-b6f7009a9330
-- title:
--   T: matrix haar right translate
-- statement:
--   The T construction uses the matrix haar right translate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/MatrixHaarRightTranslateStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/MatrixHaarRightTranslateStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MatrixHaarRightTranslate
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MatrixHaarRightTranslateStatement
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

theorem GlobalTheory.T.matrix_haar_right_translate : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → ∀ n m : ℕ, ∀ (dx : Measure (Matrix (Fin n) (Fin m) F)), dx.IsAddLeftInvariant → dx (intMat O n m) = 1 → (∀ g : GL (Fin m) F, Measure.map (fun x : Matrix (Fin n) (Fin m) F => x * (g : Matrix (Fin m) (Fin m) F)) dx = ENNReal.ofReal ((nrm (g : Matrix (Fin m) (Fin m) F).det)⁻¹ ^ n) • dx) ∧ (∀ k ∈ GLint O n, Measure.map (fun x : Matrix (Fin n) (Fin m) F => (k : Matrix (Fin n) (Fin n) F) * x) dx = dx) := by sorry
