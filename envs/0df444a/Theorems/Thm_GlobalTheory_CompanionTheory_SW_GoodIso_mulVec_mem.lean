-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_GoodIso_mulVec_mem
-- name    : GlobalTheory.CompanionTheory.SW.GoodIso.mulVec_mem
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T17:02:23.657127+00:00
-- url     : https://prove2.me/theorems/5d35c143-b09a-49be-bdef-3c11e5656426
-- title:
--   Good Iso: mul Vec mem
-- statement:
--   The Good Iso construction uses the mul Vec mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HermitianFormsIntegrallyEquivalentAlmostAll.lean#L132-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HermitianFormsIntegrallyEquivalentAlmostAll.lean#L132-L135

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_IntegralAlmostAllPlacesStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorIntegerRingAlmostAllPlacesStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianUnitFormDiagonalizesStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianUnitFormRepresentsUnitStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianFormsIntegrallyEquivalentAlmostAll
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.GoodIso

theorem GlobalTheory.CompanionTheory.SW.GoodIso.mulVec_mem {R : Type} [CommRing R] (O : Subring R) {m : ℕ} (P : Matrix (Fin m) (Fin m) R)
    (hP : ∀ i j, P i j ∈ O) (x : Fin m → R) (hx : ∀ i, x i ∈ O) (i : Fin m) : P.mulVec x i ∈ O := by sorry
