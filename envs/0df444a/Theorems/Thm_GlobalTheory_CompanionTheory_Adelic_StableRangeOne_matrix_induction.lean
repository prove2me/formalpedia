-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Adelic_StableRangeOne_matrix_induction
-- name    : GlobalTheory.CompanionTheory.Adelic.StableRangeOne.matrix_induction
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T11:16:09.593049+00:00
-- url     : https://prove2.me/theorems/6b2cb064-1d64-4109-9e0d-43a01886277c
-- title:
--   Stable Range One: matrix induction
-- statement:
--   The Stable Range One construction uses the matrix induction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/MatrixInductionTransvectionDiagonal.lean#L298-L320
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/MatrixInductionTransvectionDiagonal.lean#L298-L320

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MatrixInductionTransvectionDiagonal
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Adelic GlobalTheory.CompanionTheory.Adelic.StableRangeOne
variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.CompanionTheory.Adelic.StableRangeOne.matrix_induction :
    ∀ (R : Type) [CommRing R], (∀ a b : R, IsCoprime a b → ∃ t, IsUnit (a + t * b)) →
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (p : Matrix ι ι R → Prop),
        (∀ (i j : ι) (c : R), i ≠ j → p (Matrix.transvection i j c)) →
        (∀ D : ι → R, (∀ i, IsUnit (D i)) → p (Matrix.diagonal D)) →
        (∀ A B, IsUnit A.det → IsUnit B.det → p A → p B → p (A * B)) →
        ∀ A : Matrix ι ι R, IsUnit A.det → p A := by sorry
