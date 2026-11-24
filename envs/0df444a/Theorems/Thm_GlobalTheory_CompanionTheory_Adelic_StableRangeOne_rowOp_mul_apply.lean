-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Adelic_StableRangeOne_rowOp_mul_apply
-- name    : GlobalTheory.CompanionTheory.Adelic.StableRangeOne.rowOp_mul_apply
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:16:16.778557+00:00
-- url     : https://prove2.me/theorems/8dcb80f1-426d-4333-a0f0-c5ca101ca94c
-- title:
--   Stable Range One: row Op mul apply
-- statement:
--   The Stable Range One construction uses the row Op mul apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/MatrixInductionTransvectionDiagonal.lean#L146-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/MatrixInductionTransvectionDiagonal.lean#L146-L150

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

theorem GlobalTheory.CompanionTheory.Adelic.StableRangeOne.rowOp_mul_apply (k : ι) (c : ι → R) (A : Matrix ι ι R) (i j : ι) :
    (rowOp k c * A) i j = A i j + if i = k then ∑ l, c l * A l j else 0 := by sorry
