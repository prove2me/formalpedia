-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Adelic_StableRangeOne_mul_rowOp_apply
-- name    : GlobalTheory.CompanionTheory.Adelic.StableRangeOne.mul_rowOp_apply
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:16:18.95805+00:00
-- url     : https://prove2.me/theorems/62080a25-4a82-436a-a2de-84cd3c0479fc
-- title:
--   Stable Range One: mul row Op apply
-- statement:
--   The Stable Range One construction uses the mul row Op apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/MatrixInductionTransvectionDiagonal.lean#L158-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/MatrixInductionTransvectionDiagonal.lean#L158-L162

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

theorem GlobalTheory.CompanionTheory.Adelic.StableRangeOne.mul_rowOp_apply (k : ι) (c : ι → R) (A : Matrix ι ι R) (i j : ι) :
    (A * rowOp k c) i j = A i j + A i k * c j := by sorry
