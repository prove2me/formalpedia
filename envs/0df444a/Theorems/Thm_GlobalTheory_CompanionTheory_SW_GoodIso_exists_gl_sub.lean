-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_GoodIso_exists_gl_sub
-- name    : GlobalTheory.CompanionTheory.SW.GoodIso.exists_gl_sub
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T17:03:04.956834+00:00
-- url     : https://prove2.me/theorems/edb75dcf-8dda-4a37-af42-a469b9877bae
-- title:
--   Good Iso: exists gl sub
-- statement:
--   The Good Iso construction uses the exists gl sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HermitianFormsIntegrallyEquivalentAlmostAll.lean#L74-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HermitianFormsIntegrallyEquivalentAlmostAll.lean#L74-L116

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

theorem GlobalTheory.CompanionTheory.SW.GoodIso.exists_gl_sub {R : Type} [CommRing R] (s : R →+* R) (hs : ∀ y, s (s y) = y) (O : Subring R)
    (hO : ∀ y ∈ O, s y ∈ O) [Finite (MaximalSpectrum O)] (h2 : IsUnit (2 : O))
    (hδ : ∃ δ : O, IsUnit δ ∧ s (δ : R) = -(δ : R))
    (hN : ∀ β : O, IsUnit β → s (β : R) = β → ∃ a : O, (a : R) * s a = β)
    (m : ℕ) (K K' : Matrix (Fin m) (Fin m) R)
    (hK : ∀ i j, s (K j i) = K i j) (hK' : ∀ i j, s (K' j i) = K' i j)
    (iK : ∀ i j, K i j ∈ O) (iK' : ∀ i j, K' i j ∈ O)
    (wK : ∃ w ∈ O, K.det * w = 1) (wK' : ∃ w ∈ O, K'.det * w = 1) :
    ∃ g : GL (Fin m) R, K' = cT s (g : Matrix (Fin m) (Fin m) R) * K * (g : Matrix (Fin m) (Fin m) R) ∧
      (∀ i j, (g : Matrix (Fin m) (Fin m) R) i j ∈ O) ∧
      ∀ i j, ((g⁻¹ : GL (Fin m) R) : Matrix (Fin m) (Fin m) R) i j ∈ O := by sorry
