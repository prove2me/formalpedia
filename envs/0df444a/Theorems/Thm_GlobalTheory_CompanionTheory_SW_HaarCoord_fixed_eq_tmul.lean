-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_HaarCoord_fixed_eq_tmul
-- name    : GlobalTheory.CompanionTheory.SW.HaarCoord.fixed_eq_tmul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:30:17.021764+00:00
-- url     : https://prove2.me/theorems/5e4ee23d-4d0a-4ccd-b8f7-2a76c42988d4
-- title:
--   Haar Coord: fixed eq tmul
-- statement:
--   The Haar Coord construction uses the fixed eq tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/CoordinateHaarMeasure.lean#L69-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/CoordinateHaarMeasure.lean#L69-L114

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

theorem GlobalTheory.CompanionTheory.SW.HaarCoord.fixed_eq_tmul [CharZero F] {σ : E →ₐ[F] E} (hinv : ∀ x, σ (σ x) = x)
    (h2 : Module.finrank F E = 2) {δ : E} (hδ : δ ≠ 0) (hσδ : σ δ = -δ)
    (y : R ⊗[F] E) (hy : sigR R σ y = y) : ∃ r : R, y = r ⊗ₜ[F] (1 : E) := by sorry
