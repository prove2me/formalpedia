-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Adelic_StableRangeOne_colOp_mul_apply
-- name    : GlobalTheory.CompanionTheory.Adelic.StableRangeOne.colOp_mul_apply
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T11:16:14.937799+00:00
-- url     : https://prove2.me/theorems/87be24cf-878a-49f3-9509-d4f218437160
-- title:
--   Stable Range One: col Op mul apply
-- statement:
--   The Stable Range One construction uses the col Op mul apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/MatrixInductionTransvectionDiagonal.lean#L152-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/MatrixInductionTransvectionDiagonal.lean#L152-L156

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

theorem GlobalTheory.CompanionTheory.Adelic.StableRangeOne.colOp_mul_apply (k : ι) (c : ι → R) (A : Matrix ι ι R) (i j : ι) :
    (colOp k c * A) i j = A i j + c i * A k j := by sorry
