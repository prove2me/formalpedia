-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_gram_fiber_measures
-- name    : GlobalTheory.T.exists_gram_fiber_measures
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:30:21.345798+00:00
-- url     : https://prove2.me/theorems/93d86391-bb11-4f23-a4df-bb711595609a
-- title:
--   T: exists gram fiber measures
-- statement:
--   The T construction uses the exists gram fiber measures property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ExistsGramFiberMeasuresStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ExistsGramFiberMeasuresStatement.lean#L7-L8

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ExistsGramFiberMeasures
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ExistsGramFiberMeasuresStatement
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

theorem GlobalTheory.T.exists_gram_fiber_measures : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ) (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ∃ m, IsGramFib R σ J n μ ν m := by sorry
