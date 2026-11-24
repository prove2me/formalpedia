-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_Fact_measurable_actW_consTup
-- name    : GlobalTheory.CompanionTheory.SW.Fact.measurable_actW_consTup
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:03:47.842781+00:00
-- url     : https://prove2.me/theorems/b6e9d5c5-5451-427b-9327-d586524f8dbb
-- title:
--   Fact: measurable act W cons Tup
-- statement:
--   The Fact construction uses the measurable act W cons Tup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/UnitaryActionConsTupleMeasurable.lean#L19-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/UnitaryActionConsTupleMeasurable.lean#L19-L31

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitaryActionConsTupleMeasurable
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Fact

theorem GlobalTheory.CompanionTheory.SW.Fact.measurable_actW_consTup : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (g : HA R σ J), Measurable (fun X : Fin n → Fin M → R ⊗[F] E => actW R σ J g (consTup X)) := by sorry
