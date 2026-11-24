-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_GramEmpty_fibre_gram_zero
-- name    : GlobalTheory.CompanionTheory.SW.GramEmpty.fibre_gram_zero
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:06:22.63712+00:00
-- url     : https://prove2.me/theorems/e6cc8629-5887-4db4-813a-046c84c49ae8
-- title:
--   Gram Empty: fibre gram zero
-- statement:
--   The Gram Empty construction uses the fibre gram zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/RankZeroGramFiberMeasure.lean#L30-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/RankZeroGramFiberMeasure.lean#L30-L56

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_RankZeroGramFiberMeasure
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
open GlobalTheory.CompanionTheory.SW.GramEmpty

theorem GlobalTheory.CompanionTheory.SW.GramEmpty.fibre_gram_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ (lam : Measure R), lam.IsAddHaarMeasure → ∀ m, IsGramFib R σ J 0 (coordW R b lam 0 M) (coordHerm R σ b lam 0) m → ∀ S, m S = Measure.dirac (fun a => a.elim0) := by sorry
