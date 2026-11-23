-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_HaarCoord_hermMat_mem
-- name    : GlobalTheory.CompanionTheory.SW.HaarCoord.hermMat_mem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:55.047894+00:00
-- url     : https://prove2.me/theorems/e2810ccc-cb61-48d6-8797-11a75ba33273
-- title:
--   Haar Coord: herm Mat mem
-- statement:
--   The Haar Coord construction uses the herm Mat mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/CoordinateHaarMeasure.lean#L139-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/CoordinateHaarMeasure.lean#L139-L149

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinateHaarMeasure
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.HaarCoord
variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable (R : Type) [CommRing R] [Algebra F R]

theorem GlobalTheory.CompanionTheory.SW.HaarCoord.hermMat_mem {σ : E →ₐ[F] E} (hinv : ∀ x, σ (σ x) = x) (n : ℕ)
    (x : (Fin n → R) × ({p : Fin n × Fin n // p.1 < p.2} → R ⊗[F] E)) :
    hermMat R σ n x ∈ HermR R σ n := by sorry
