-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Adelic_StableRangeOne_colOp_mem
-- name    : GlobalTheory.CompanionTheory.Adelic.StableRangeOne.colOp_mem
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:16:07.01281+00:00
-- url     : https://prove2.me/theorems/bb83a8ae-0111-4b82-99d5-41e189be6ed8
-- title:
--   Stable Range One: col Op mem
-- statement:
--   The Stable Range One construction uses the col Op mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/MatrixInductionTransvectionDiagonal.lean#L110-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/MatrixInductionTransvectionDiagonal.lean#L110-L144

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

theorem GlobalTheory.CompanionTheory.Adelic.StableRangeOne.colOp_mem (k : ι) (c : ι → R) (hc : c k = 0) : colOp k c ∈ elem R ι := by sorry
