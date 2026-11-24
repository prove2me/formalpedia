-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_LDL_gram_eq
-- name    : GlobalTheory.CompanionTheory.SW.LDL.gram_eq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T12:07:37.119074+00:00
-- url     : https://prove2.me/theorems/62704f91-1a81-4d4a-b375-e82376e0b552
-- title:
--   LDL: gram eq
-- statement:
--   The LDL construction uses the gram eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HermitianOpenChartDiagonalUnipotent.lean#L131-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HermitianOpenChartDiagonalUnipotent.lean#L131-L137

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorInvolutionAlgebraPropertiesStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianOpenChartDiagonalUnipotent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.LDL
variable {R K : Type} [CommRing R] [CommRing K]
variable (ι : R →+* K) (τ : K →+* K)
variable {ι τ}

theorem GlobalTheory.CompanionTheory.SW.LDL.gram_eq (ι : R →+* K) (τ : K →+* K) {n : ℕ} (d : Fin n → Rˣ) (u : Up n → K) :
    gram ι τ d u = cT τ (unip u) * Matrix.diagonal (fun i => ι (d i)) * unip u := by sorry
