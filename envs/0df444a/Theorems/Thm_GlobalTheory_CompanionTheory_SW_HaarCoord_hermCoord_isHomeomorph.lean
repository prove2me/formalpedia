-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_HaarCoord_hermCoord_isHomeomorph
-- name    : GlobalTheory.CompanionTheory.SW.HaarCoord.hermCoord_isHomeomorph
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:05:38.5075+00:00
-- url     : https://prove2.me/theorems/a30c0d38-0b5e-42b9-ab3f-2b7a9f1be251
-- title:
--   Haar Coord: herm Coord is Homeomorph
-- statement:
--   The Haar Coord construction uses the herm Coord is Homeomorph property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/CoordinateHaarMeasure.lean#L167-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/CoordinateHaarMeasure.lean#L167-L222

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
variable [TopologicalSpace R]

theorem GlobalTheory.CompanionTheory.SW.HaarCoord.hermCoord_isHomeomorph [IsTopologicalRing R] [CharZero F] {σ : E →ₐ[F] E}
    (hinv : ∀ x, σ (σ x) = x) (h2 : Module.finrank F E = 2) {δ : E} (hδ : δ ≠ 0) (hσδ : σ δ = -δ)
    (n : ℕ) [ContinuousAdd (R ⊗[F] E)] [ContinuousSMul R (R ⊗[F] E)]
    (hsig : Continuous (sigR R σ)) (htr : Continuous (Algebra.trace R (R ⊗[F] E))) :
    IsHomeomorph (hermCoord R σ n) := by sorry
