-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_HaarCoord_conj_facts
-- name    : GlobalTheory.CompanionTheory.SW.HaarCoord.conj_facts
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:30:40.913608+00:00
-- url     : https://prove2.me/theorems/de7fda01-2068-468e-a931-2423a1153ea2
-- title:
--   Haar Coord: conj facts
-- statement:
--   The Haar Coord construction uses the conj facts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/CoordinateHaarMeasure.lean#L27-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/CoordinateHaarMeasure.lean#L27-L48

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

theorem GlobalTheory.CompanionTheory.SW.HaarCoord.conj_facts [NumberField F] [NumberField E] {σ : E →ₐ[F] E} (h : IsCMExt F E σ) :
    (∀ x, σ (σ x) = x) ∧ ∃ δ : E, δ ≠ 0 ∧ σ δ = -δ := by sorry
