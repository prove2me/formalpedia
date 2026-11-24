-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Adelic_OrthHaar_scale_transpose
-- name    : GlobalTheory.CompanionTheory.Adelic.OrthHaar.scale_transpose
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:16:26.49359+00:00
-- url     : https://prove2.me/theorems/712d14d8-7457-4e36-aa1a-41e55c5835a3
-- title:
--   Orth Haar: scale transpose
-- statement:
--   The Orth Haar construction uses the scale transpose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/MapMulVecEqOfTransposeMulMulEq.lean#L111-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/MapMulVecEqOfTransposeMulMulEq.lean#L111-L122

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MatrixInductionTransvectionDiagonalStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MapMulVecEqOfTransposeMulMulEq
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Adelic GlobalTheory.CompanionTheory.Adelic.OrthHaar
variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
  [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.CompanionTheory.Adelic.OrthHaar.scale_transpose (hsr : ∀ a b : R, IsCoprime a b → ∃ t, IsUnit (a + t * b))
    (A : Matrix ι ι R) (hA : IsUnit A.det) : scale Aᵀ = scale A := by sorry
