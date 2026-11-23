-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Equi_LatSum_scal_apply
-- name    : GlobalTheory.CompanionTheory.Equi.LatSum.scal_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:45:06.789951+00:00
-- url     : https://prove2.me/theorems/eb926163-d013-401a-8bcb-4d20b6aa730a
-- title:
--   Lat Sum: scal apply
-- statement:
--   The Lat Sum construction uses the scal apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LatticeCosetScaledRiemannSum.lean#L77-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LatticeCosetScaledRiemannSum.lean#L77-L77

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetOff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LatticePointCountScalingStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ArchimedeanFundamentalDomainIntegersStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ScalingMeasureProductArchimedeanStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteAdelesLocalRingTotallyReal
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LatticeCosetScaledRiemannSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Equi GlobalTheory.CompanionTheory.Equi.LatSum

theorem GlobalTheory.CompanionTheory.Equi.LatSum.scal_apply {R ι : Type} [CommRing R] (t : R) (y : ι → R) (i : ι) : scal ι t y i = t * y i := by sorry

attribute [defeq] GlobalTheory.CompanionTheory.Equi.LatSum.scal_apply
