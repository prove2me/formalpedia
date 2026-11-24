-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_OneHerm_map_hermScal
-- name    : GlobalTheory.CompanionTheory.SW.OneHerm.map_hermScal
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:07:35.434916+00:00
-- url     : https://prove2.me/theorems/6b9f6d43-bfe2-4ba2-b4cc-ad1af4fb55f5
-- title:
--   One Herm: map herm Scal
-- statement:
--   The One Herm construction uses the map herm Scal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ContinuousHermScal.lean#L176-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ContinuousHermScal.lean#L176-L229

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ContinuousHermScal
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.OneHerm
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
  [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R]

theorem GlobalTheory.CompanionTheory.SW.OneHerm.map_hermScal {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E)
    (lam : Measure R) [lam.IsAddHaarMeasure] :
    lam.map (hermScal R σ) = coordHerm R σ b lam 1 := by sorry
