-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_GoodIso_exists_gl_equiv
-- name    : GlobalTheory.CompanionTheory.SW.GoodIso.exists_gl_equiv
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T17:03:04.713892+00:00
-- url     : https://prove2.me/theorems/e6468f38-2215-4fe4-b95b-231297c5411d
-- title:
--   Good Iso: exists gl equiv
-- statement:
--   The Good Iso construction uses the exists gl equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HermitianFormsIntegrallyEquivalentAlmostAll.lean#L48-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HermitianFormsIntegrallyEquivalentAlmostAll.lean#L48-L72

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

theorem GlobalTheory.CompanionTheory.SW.GoodIso.exists_gl_equiv (A : Type) [CommRing A] [Finite (MaximalSpectrum A)] (σ : A →+* A)
    (hσ : ∀ y, σ (σ y) = y) (h2 : IsUnit (2 : A)) (hδ : ∃ δ : A, IsUnit δ ∧ σ δ = -δ)
    (hN : ∀ β : A, IsUnit β → σ β = β → ∃ a : A, a * σ a = β)
    (m : ℕ) (J J' : Matrix (Fin m) (Fin m) A) (hJ : ∀ i j, σ (J j i) = J i j) (hd : IsUnit J.det)
    (hJ' : ∀ i j, σ (J' j i) = J' i j) (hd' : IsUnit J'.det) :
    ∃ G : GL (Fin m) A,
      J' = cT σ (G : Matrix (Fin m) (Fin m) A) * J * (G : Matrix (Fin m) (Fin m) A) := by sorry
