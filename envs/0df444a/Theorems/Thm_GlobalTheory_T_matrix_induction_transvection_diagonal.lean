-- Prove2me | Theorems.Thm_GlobalTheory_T_matrix_induction_transvection_diagonal
-- name    : GlobalTheory.T.matrix_induction_transvection_diagonal
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T20:52:44.846031+00:00
-- url     : https://prove2.me/theorems/c9f81c6a-c629-4477-919d-5889d768aba4
-- title:
--   T: matrix induction transvection diagonal
-- statement:
--   The T construction uses the matrix induction transvection diagonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/MatrixInductionTransvectionDiagonalStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/MatrixInductionTransvectionDiagonalStatement.lean#L6-L7

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MatrixInductionTransvectionDiagonal
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MatrixInductionTransvectionDiagonalStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.matrix_induction_transvection_diagonal : ∀ (R : Type) [CommRing R], (∀ a b : R, IsCoprime a b → ∃ t, IsUnit (a + t * b)) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (p : Matrix ι ι R → Prop), (∀ (i j : ι) (c : R), i ≠ j → p (Matrix.transvection i j c)) → (∀ D : ι → R, (∀ i, IsUnit (D i)) → p (Matrix.diagonal D)) → (∀ A B, IsUnit A.det → IsUnit B.det → p A → p B → p (A * B)) → ∀ A : Matrix ι ι R, IsUnit A.det → p A := by sorry
