-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Adelic_OrthHaar_transvection_mulVec_apply
-- name    : GlobalTheory.CompanionTheory.Adelic.OrthHaar.transvection_mulVec_apply
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:16:30.248275+00:00
-- url     : https://prove2.me/theorems/ff0d03c4-d6cd-4a44-a7ba-b942c0a25fac
-- title:
--   Orth Haar: transvection mul Vec apply
-- statement:
--   The Orth Haar construction uses the transvection mul Vec apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/MapMulVecEqOfTransposeMulMulEq.lean#L23-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/MapMulVecEqOfTransposeMulMulEq.lean#L23-L28

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
variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.CompanionTheory.Adelic.OrthHaar.transvection_mulVec_apply (i j : ι) (c : R) (f : ι → R) (k : ι) :
    (Matrix.transvection i j c *ᵥ f) k = f k + if k = i then c * f j else 0 := by sorry
