-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_GoodRing_exists_good_nat
-- name    : GlobalTheory.CompanionTheory.SW.GoodRing.exists_good_nat
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T14:03:13.632835+00:00
-- url     : https://prove2.me/theorems/9ee8ecd0-0f1e-4b8c-8759-730ebdf1fccb
-- title:
--   Good Ring: exists good nat
-- statement:
--   The Good Ring construction uses the exists good nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/TensorIntegerRingAlmostAllPlaces.lean#L12-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/TensorIntegerRingAlmostAllPlaces.lean#L12-L67

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

theorem GlobalTheory.CompanionTheory.SW.GoodRing.exists_good_nat {k : Type} [Field k] (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (D A B C : k)
    (hne : A ≠ 0 ∨ B ≠ 0 ∨ C ≠ 0) :
    ∃ a : ℕ, 1 - D * (a : k) ^ 2 ≠ 0 ∧ A + B * (a : k) + C * (a : k) ^ 2 ≠ 0 := by sorry
