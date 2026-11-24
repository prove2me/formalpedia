-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_GoodRing_exists_eps
-- name    : GlobalTheory.CompanionTheory.SW.GoodRing.exists_eps
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T14:01:59.738799+00:00
-- url     : https://prove2.me/theorems/671cbb1a-c31d-4dec-875c-47d580c112fa
-- title:
--   Good Ring: exists eps
-- statement:
--   The Good Ring construction uses the exists eps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/TensorIntegerRingAlmostAllPlaces.lean#L121-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/TensorIntegerRingAlmostAllPlaces.lean#L121-L202

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

theorem GlobalTheory.CompanionTheory.SW.GoodRing.exists_eps [IsLocalRing R] (hδ : δ * δ = ι D) (hτι : ∀ r, τ (ι r) = ι r) (hτδ : τ δ = -δ)
    (hsp : ∀ y : O, ∃ p q : R, y = ι p + ι q * δ)
    (hinj : ∀ p q : R, ι p + ι q * δ = 0 → p = 0 ∧ q = 0)
    (hD : IsUnit D) (h2 : IsUnit (2 : R)) (h3 : IsUnit (3 : R))
    (s β : O) (hβ : IsUnit β) (hτβ : τ β = β) :
    ∃ ε z : O, ε * τ ε = 1 ∧ (β - τ ε * s) * z = 1 := by sorry
