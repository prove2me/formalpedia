-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimInf_unimodular_mod_units_inf
-- name    : GlobalTheory.CompanionTheory.SW.PrimInf.unimodular_mod_units_inf
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:07:48.413274+00:00
-- url     : https://prove2.me/theorems/99f82ca9-0770-44e9-b268-16bcb7e14ba8
-- title:
--   Prim Inf: unimodular mod units inf
-- statement:
--   The Prim Inf construction uses the unimodular mod units inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ArchimedeanPrimitiveVectorCompactRescale.lean#L283-L286
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ArchimedeanPrimitiveVectorCompactRescale.lean#L283-L286

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

theorem GlobalTheory.CompanionTheory.SW.PrimInf.unimodular_mod_units_inf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ), ∃ Ω : Set (Fin 1 → Fin M → Ainf F ⊗[F] E), IsCompact Ω ∧ ∀ y : Fin 1 → Fin M → Ainf F ⊗[F] E, (∃ z : Fin M → Ainf F ⊗[F] E, z ⬝ᵥ y 0 = 1) → ∃ (a : (Ainf F ⊗[F] E)ˣ) (z : Fin 1 → Fin M → Ainf F ⊗[F] E), (a : Ainf F ⊗[F] E) • y ∈ Ω ∧ z ∈ Ω ∧ z 0 ⬝ᵥ ((a : Ainf F ⊗[F] E) • y) 0 = 1 := by sorry
