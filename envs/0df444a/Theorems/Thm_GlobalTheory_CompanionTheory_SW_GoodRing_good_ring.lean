-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_GoodRing_good_ring
-- name    : GlobalTheory.CompanionTheory.SW.GoodRing.good_ring
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T14:03:35.411336+00:00
-- url     : https://prove2.me/theorems/2372ce02-5027-4c5c-8d1a-984cfa210497
-- title:
--   Good Ring: good ring
-- statement:
--   The Good Ring construction uses the good ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/TensorIntegerRingAlmostAllPlaces.lean#L405-L429
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/TensorIntegerRingAlmostAllPlaces.lean#L405-L429

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_IntegralAlmostAllPlacesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_QuadraticExtNormFormOverAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_UnitNormFormAtOddPlace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthRestrictScalarsEqSumInertiaDegOfSubset
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorIntegerRingAlmostAllPlaces
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.GoodRing

theorem GlobalTheory.CompanionTheory.SW.GoodRing.good_ring : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∃ O : Subring (Fv F v ⊗[F] E), (∀ y, y ∈ O ↔ ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈ v.adicCompletionIntegers F) ∧ (∀ y ∈ O, sigR (Fv F v) σ y ∈ O) ∧ Finite (MaximalSpectrum O) ∧ IsUnit (2 : O) ∧ (∃ δ : O, IsUnit δ ∧ sigR (Fv F v) σ δ = -δ) ∧ (∀ s β : O, IsUnit β → sigR (Fv F v) σ β = β → ∃ ε z : O, (ε : Fv F v ⊗[F] E) * sigR (Fv F v) σ ε = 1 ∧ ((β : Fv F v ⊗[F] E) - sigR (Fv F v) σ ε * s) * z = 1) ∧ ∀ β : O, IsUnit β → sigR (Fv F v) σ β = β → ∃ a : O, (a : Fv F v ⊗[F] E) * sigR (Fv F v) σ a = β := by sorry
