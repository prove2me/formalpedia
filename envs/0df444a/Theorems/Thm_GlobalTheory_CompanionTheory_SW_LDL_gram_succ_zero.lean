-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_LDL_gram_succ_zero
-- name    : GlobalTheory.CompanionTheory.SW.LDL.gram_succ_zero
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T12:06:38.863251+00:00
-- url     : https://prove2.me/theorems/49f413a3-e48b-436e-8e21-0f674ae7ed25
-- title:
--   LDL: gram succ zero
-- statement:
--   The LDL construction uses the gram succ zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HermitianOpenChartDiagonalUnipotent.lean#L86-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HermitianOpenChartDiagonalUnipotent.lean#L86-L88

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

theorem GlobalTheory.CompanionTheory.SW.LDL.gram_succ_zero {n : ℕ} (d : Fin (n + 1) → Rˣ) (u : Up (n + 1) → K) (i : Fin n) :
    gram ι τ d u i.succ 0 = τ (headU u i) * ι (d 0) := by sorry
