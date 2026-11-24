-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_GoodRing_coord_mem
-- name    : GlobalTheory.CompanionTheory.SW.GoodRing.coord_mem
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T14:03:04.771802+00:00
-- url     : https://prove2.me/theorems/3aa19a58-b589-47b1-94ce-2b102c231e0f
-- title:
--   Good Ring: coord mem
-- statement:
--   The Good Ring construction uses the coord mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/TensorIntegerRingAlmostAllPlaces.lean#L210-L216
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/TensorIntegerRingAlmostAllPlaces.lean#L210-L216

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

theorem GlobalTheory.CompanionTheory.SW.GoodRing.coord_mem {ι₁ ι₂ : Type} [Fintype ι₁] (P : Module.Basis ι₁ K A) (Q : Module.Basis ι₂ K A)
    (hPQ : ∀ i l, Q.repr (P i) l ∈ R) (y : A) (hy : ∀ i, P.repr y i ∈ R) (l : ι₂) :
    Q.repr y l ∈ R := by sorry
