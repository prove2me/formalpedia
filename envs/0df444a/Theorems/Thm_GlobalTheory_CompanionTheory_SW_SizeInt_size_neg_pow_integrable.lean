-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_SizeInt_size_neg_pow_integrable
-- name    : GlobalTheory.CompanionTheory.SW.SizeInt.size_neg_pow_integrable
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:10:19.121024+00:00
-- url     : https://prove2.me/theorems/e985eda5-489e-4431-8ca1-9ccfe493e06b
-- title:
--   Size Int: size neg pow integrable
-- statement:
--   The Size Int construction uses the size neg pow integrable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/SizeFunctionRapidDecayIntegrable.lean#L118-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/SizeFunctionRapidDecayIntegrable.lean#L118-L171

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SizeFunctionRapidDecayIntegrable
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
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.SizeInt
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem GlobalTheory.CompanionTheory.SW.SizeInt.size_neg_pow_integrable : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ (n M : ℕ) (μ : Measure (Fin n → Fin M → Ainf F ⊗[F] E)), μ.IsAddHaarMeasure → Continuous (sizeTup b : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ) ∧ (∀ X : Fin n → Fin M → Ainf F ⊗[F] E, 0 ≤ sizeTup b X) ∧ ∃ N : ℕ, ∫⁻ X, ENNReal.ofReal (((1 + sizeTup b X) ^ N)⁻¹) ∂μ < ⊤ := by sorry
