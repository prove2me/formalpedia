-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Equi_InfScale_map_theta_mul
-- name    : GlobalTheory.CompanionTheory.Equi.InfScale.map_theta_mul
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:39:14.273454+00:00
-- url     : https://prove2.me/theorems/01cd6648-94e3-4f2e-85d6-6b10d64a34a7
-- title:
--   Inf Scale: map theta mul
-- statement:
--   The Inf Scale construction uses the map theta mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ScalingMeasureProductArchimedean.lean#L25-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ScalingMeasureProductArchimedean.lean#L25-L57

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetOff
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteAdelesLocalRingTotallyReal
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ScalingMeasureProductArchimedean
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Equi GlobalTheory.CompanionTheory.Equi.InfScale
open GlobalTheory.CompanionTheory.SW.LocInf

theorem GlobalTheory.CompanionTheory.Equi.InfScale.map_theta_mul {F : Type} [Field F] [NumberField F] (h : IsTotallyReal F) (θ : ℝ →+* Ainf F)
    (li : Measure (Ainf F)) [li.IsAddHaarMeasure] {ε : ℝ} (hε : 0 < ε) :
    Measure.map (fun y : Ainf F => θ ε * y) li =
      ENNReal.ofReal ((ε ^ Module.finrank ℚ F)⁻¹) • li := by sorry
