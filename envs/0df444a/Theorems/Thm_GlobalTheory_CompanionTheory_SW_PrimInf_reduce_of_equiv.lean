-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimInf_reduce_of_equiv
-- name    : GlobalTheory.CompanionTheory.SW.PrimInf.reduce_of_equiv
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:07:51.060799+00:00
-- url     : https://prove2.me/theorems/ca794a34-ab85-49f0-b2da-f16467e86f72
-- title:
--   Prim Inf: reduce of equiv
-- statement:
--   The Prim Inf construction uses the reduce of equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ArchimedeanPrimitiveVectorCompactRescale.lean#L12-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ArchimedeanPrimitiveVectorCompactRescale.lean#L12-L92

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRing
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ArchimedeanPrimitiveVectorCompactRescale
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PrimInf
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem GlobalTheory.CompanionTheory.SW.PrimInf.reduce_of_equiv {K : Type} [CommRing K] [TopologicalSpace K] {W : Type} [Fintype W]
    (Φ : K ≃+* (W → ℂ)) (hΦ : IsHomeomorph Φ) (M : ℕ) :
    ∃ Ω : Set (Fin 1 → Fin M → K), IsCompact Ω ∧ ∀ y : Fin 1 → Fin M → K,
      (∃ z : Fin M → K, z ⬝ᵥ y 0 = 1) →
      ∃ (a : Kˣ) (z : Fin 1 → Fin M → K), (a : K) • y ∈ Ω ∧ z ∈ Ω ∧ z 0 ⬝ᵥ ((a : K) • y) 0 = 1 := by sorry
