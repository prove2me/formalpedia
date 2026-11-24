-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_GoodRing_exists_subring
-- name    : GlobalTheory.CompanionTheory.SW.GoodRing.exists_subring
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T14:01:50.253959+00:00
-- url     : https://prove2.me/theorems/2df7fbbf-9033-4f46-a5ff-41a8de53d9b1
-- title:
--   Good Ring: exists subring
-- statement:
--   The Good Ring construction uses the exists subring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/TensorIntegerRingAlmostAllPlaces.lean#L231-L272
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/TensorIntegerRingAlmostAllPlaces.lean#L231-L272

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
variable {K A : Type} [Field K] [CommRing A] [Algebra K A] (R : Subring K)

theorem GlobalTheory.CompanionTheory.SW.GoodRing.exists_subring {d : ℕ} (B : Module.Basis (Fin 2) K A) (C : Module.Basis (Fin d) K A)
    (D : K) (hB0 : B 0 = 1) (hD : B 1 * B 1 = algebraMap K A D) (hDR : D ∈ R)
    (hBC : ∀ k j, B.repr (C k) j ∈ R) (hCB : ∀ j k, C.repr (B j) k ∈ R) :
    ∃ O : Subring A, (∀ y, y ∈ O ↔ ∀ k, C.repr y k ∈ R) ∧ (∀ y, y ∈ O ↔ ∀ j, B.repr y j ∈ R) := by sorry
