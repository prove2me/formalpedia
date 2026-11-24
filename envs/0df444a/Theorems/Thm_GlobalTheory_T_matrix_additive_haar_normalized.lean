-- Prove2me | Theorems.Thm_GlobalTheory_T_matrix_additive_haar_normalized
-- name    : GlobalTheory.T.matrix_additive_haar_normalized
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T14:02:31.929734+00:00
-- url     : https://prove2.me/theorems/1c317398-e6df-478c-8eaf-0c2b2fbc7f72
-- title:
--   T: matrix additive haar normalized
-- statement:
--   The T construction uses the matrix additive haar normalized property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/MatrixAdditiveHaarNormalizedStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/MatrixAdditiveHaarNormalizedStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MatrixAdditiveHaarNormalized
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MatrixAdditiveHaarNormalizedStatement
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

theorem GlobalTheory.T.matrix_additive_haar_normalized : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → ∀ n m : ℕ, BorelSpace (Matrix (Fin n) (Fin m) F) ∧ IsOpen (intMat O n m) ∧ IsCompact (intMat O n m) ∧ (∃ dx : Measure (Matrix (Fin n) (Fin m) F), dx.IsAddLeftInvariant ∧ dx (intMat O n m) = 1) ∧ (∀ (dx : Measure (Matrix (Fin n) (Fin m) F)), dx.IsAddLeftInvariant → dx (intMat O n m) = 1 → dx.IsAddHaarMeasure) ∧ (∀ (dx : Measure (Matrix (Fin n) (Fin m) F)), dx.IsAddLeftInvariant → dx (intMat O n m) = 1 → ∀ (dy : Measure (Matrix (Fin n) (Fin m) F)), dy.IsAddLeftInvariant → dy (intMat O n m) = 1 → dx = dy) := by sorry
