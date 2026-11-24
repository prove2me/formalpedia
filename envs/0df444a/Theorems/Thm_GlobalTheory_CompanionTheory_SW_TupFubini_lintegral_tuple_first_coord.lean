-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_TupFubini_lintegral_tuple_first_coord
-- name    : GlobalTheory.CompanionTheory.SW.TupFubini.lintegral_tuple_first_coord
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T12:11:57.392527+00:00
-- url     : https://prove2.me/theorems/e9b10d86-0e99-449b-ad34-71ea938ae7ce
-- title:
--   Tup Fubini: lintegral tuple first coord
-- statement:
--   The Tup Fubini construction uses the lintegral tuple first coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberMeasureOrthogonalExtension.lean#L46-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberMeasureOrthogonalExtension.lean#L46-L84

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinateHaarMeasureStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitaryActionPreservesHaarLocalStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicUnitaryGroupLocallyCompactStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasureOrthogonalExtension
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.TupFubini
variable {T : Type} [MeasurableSpace T]

theorem GlobalTheory.CompanionTheory.SW.TupFubini.lintegral_tuple_first_coord (m : Measure T) [SigmaFinite m] (n M : ℕ)
    (ψ : (Fin n → Fin (M + 1) → T) → ℝ≥0∞) (hψ : Measurable ψ) :
    ∫⁻ Y, ψ Y ∂(Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin (M + 1) => m) =
      ∫⁻ c : Fin n → T, ∫⁻ X : Fin n → Fin M → T, ψ (fun a => Fin.cons (c a) (X a))
        ∂(Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin M => m)
        ∂(Measure.pi fun _ : Fin n => m) := by sorry
