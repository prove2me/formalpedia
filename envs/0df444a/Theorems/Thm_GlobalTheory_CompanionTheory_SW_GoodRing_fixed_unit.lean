-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_GoodRing_fixed_unit
-- name    : GlobalTheory.CompanionTheory.SW.GoodRing.fixed_unit
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T14:03:56.655987+00:00
-- url     : https://prove2.me/theorems/a7d8f378-1a4f-4c4c-84dd-e713515fcc14
-- title:
--   Good Ring: fixed unit
-- statement:
--   The Good Ring construction uses the fixed unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/TensorIntegerRingAlmostAllPlaces.lean#L99-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/TensorIntegerRingAlmostAllPlaces.lean#L99-L119

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
variable {R O : Type} [CommRing R] [CommRing O] (ι : R →+* O) (τ : O →+* O) (δ : O) (D : R)

theorem GlobalTheory.CompanionTheory.SW.GoodRing.fixed_unit (hτι : ∀ r, τ (ι r) = ι r) (hτδ : τ δ = -δ)
    (hsp : ∀ y : O, ∃ p q : R, y = ι p + ι q * δ)
    (hinj : ∀ p q : R, ι p + ι q * δ = 0 → p = 0 ∧ q = 0) (h2 : IsUnit (2 : R))
    (β : O) (hβ : IsUnit β) (hτβ : τ β = β) : ∃ b : R, IsUnit b ∧ β = ι b := by sorry
