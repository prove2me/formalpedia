-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_ScaleCont_fibre_scale_continuous
-- name    : GlobalTheory.CompanionTheory.SW.ScaleCont.fibre_scale_continuous
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:09:47.040418+00:00
-- url     : https://prove2.me/theorems/4c4d3fbd-303a-4f18-bcc4-14b4ed6dd48f
-- title:
--   Scale Cont: fibre scale continuous
-- statement:
--   The Scale Cont construction uses the fibre scale continuous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberMeasuresIntegralFormula.lean#L129-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberMeasuresIntegralFormula.lean#L129-L193

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HaarModularCharacterOfContinuousActionStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianMatricesLocallyCompactBorelStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramRightActionIdentitiesStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasuresSupportStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasuresIntegralFormula
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.ScaleCont

theorem GlobalTheory.CompanionTheory.SW.ScaleCont.fibre_scale_continuous : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ), ∀ (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)) (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFib R σ J n μ ν m → ∃ κ : GL (Fin n) (R ⊗[F] E) → ℝ≥0, Continuous κ ∧ (∀ g, κ g ≠ 0) ∧ κ 1 = 1 ∧ ∀ (g : GL (Fin n) (R ⊗[F] E)) (S S' : HermR R σ n), (S' : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = cT (sigR R σ) (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) → m S' = κ g • (m S).map (fun X => rmul R X (g : Matrix (Fin n) (Fin n) (R ⊗[F] E))) := by sorry
