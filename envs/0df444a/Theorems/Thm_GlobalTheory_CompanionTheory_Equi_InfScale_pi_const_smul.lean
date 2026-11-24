-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Equi_InfScale_pi_const_smul
-- name    : GlobalTheory.CompanionTheory.Equi.InfScale.pi_const_smul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:38:54.000305+00:00
-- url     : https://prove2.me/theorems/e9718873-5a0b-483e-bd46-a6dc13df25a7
-- title:
--   Inf Scale: pi const smul
-- statement:
--   The Inf Scale construction uses the pi const smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ScalingMeasureProductArchimedean.lean#L59-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ScalingMeasureProductArchimedean.lean#L59-L64

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

theorem GlobalTheory.CompanionTheory.Equi.InfScale.pi_const_smul {X : Type} [MeasurableSpace X] (ι : Type) [Fintype ι] (μ : Measure X) [SigmaFinite μ]
    (c : ENNReal) [SigmaFinite (c • μ)] :
    (Measure.pi fun _ : ι => c • μ) = c ^ Fintype.card ι • Measure.pi fun _ : ι => μ := by sorry
