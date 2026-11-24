-- Prove2me | Theorems.Thm_GlobalTheory_T_archimedean_primitive_vector_compact_rescale
-- name    : GlobalTheory.T.archimedean_primitive_vector_compact_rescale
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:26:53.541821+00:00
-- url     : https://prove2.me/theorems/b45c36ea-4394-40e2-81a9-f8da5563b7d9
-- title:
--   T: archimedean primitive vector compact rescale
-- statement:
--   The T construction uses the archimedean primitive vector compact rescale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ArchimedeanPrimitiveVectorCompactRescaleStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ArchimedeanPrimitiveVectorCompactRescaleStatement.lean#L7-L8

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ArchimedeanPrimitiveVectorCompactRescale
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ArchimedeanPrimitiveVectorCompactRescaleStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.archimedean_primitive_vector_compact_rescale : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ), ∃ Ω : Set (Fin 1 → Fin M → Ainf F ⊗[F] E), IsCompact Ω ∧ ∀ y : Fin 1 → Fin M → Ainf F ⊗[F] E, (∃ z : Fin M → Ainf F ⊗[F] E, z ⬝ᵥ y 0 = 1) → ∃ (a : (Ainf F ⊗[F] E)ˣ) (z : Fin 1 → Fin M → Ainf F ⊗[F] E), (a : Ainf F ⊗[F] E) • y ∈ Ω ∧ z ∈ Ω ∧ z 0 ⬝ᵥ ((a : Ainf F ⊗[F] E) • y) 0 = 1 := by sorry
