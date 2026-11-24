-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_coordW_one_map_coords
-- name    : GlobalTheory.CompanionTheory.SW.coordW_one_map_coords
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:13:08.968085+00:00
-- url     : https://prove2.me/theorems/386a9049-cff3-4dca-99da-786c962d7381
-- title:
--   SW: coord W one map coords
-- statement:
--   The SW construction uses the coord W one map coords property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/MeasurableCoordinateMapsTensor.lean#L28-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/MeasurableCoordinateMapsTensor.lean#L28-L60

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MeasurableCoordinateMapsTensor
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW

theorem GlobalTheory.CompanionTheory.SW.coordW_one_map_coords : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R], ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ (M : ℕ) (lam : Measure R), lam.IsAddHaarMeasure → (Measurable fun (X : Fin 1 → Fin M → R ⊗[F] E) (p : Fin M × Fin d) => (Algebra.TensorProduct.basis R b).repr (X 0 p.1) p.2) ∧ (coordW R b lam 1 M).map (fun X (p : Fin M × Fin d) => (Algebra.TensorProduct.basis R b).repr (X 0 p.1) p.2) = Measure.pi fun _ => lam := by sorry
