-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Adelic_OrthHaar_transpose_transvection
-- name    : GlobalTheory.CompanionTheory.Adelic.OrthHaar.transpose_transvection
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:16:26.255663+00:00
-- url     : https://prove2.me/theorems/0c4fbaf0-d0bd-4830-9c54-e37df8bc55ee
-- title:
--   Orth Haar: transpose transvection
-- statement:
--   The Orth Haar construction uses the transpose transvection property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/MapMulVecEqOfTransposeMulMulEq.lean#L107-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/MapMulVecEqOfTransposeMulMulEq.lean#L107-L109

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

theorem GlobalTheory.CompanionTheory.Adelic.OrthHaar.transpose_transvection (i j : ι) (c : R) :
    (Matrix.transvection i j c)ᵀ = Matrix.transvection j i c := by sorry
