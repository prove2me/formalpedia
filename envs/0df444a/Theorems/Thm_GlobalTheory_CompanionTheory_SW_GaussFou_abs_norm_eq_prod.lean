-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_GaussFou_abs_norm_eq_prod
-- name    : GlobalTheory.CompanionTheory.SW.GaussFou.abs_norm_eq_prod
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T12:05:19.767483+00:00
-- url     : https://prove2.me/theorems/c1590a2c-219f-4761-a992-3b190f459b77
-- title:
--   Gauss Fou: abs norm eq prod
-- statement:
--   The Gauss Fou construction uses the abs norm eq prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ArchimedeanGaussianFourier.lean#L27-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ArchimedeanGaussianFourier.lean#L27-L34

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_RealGaussianFourierTransformStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ArchimedeanGaussianFourier
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.GaussFou
variable {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.CompanionTheory.SW.GaussFou.abs_norm_eq_prod (hF : IsTotallyReal F) (ρ : InfinitePlace F → (F →+* ℝ))
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) (a : F) :
    |((Algebra.norm ℚ a : ℚ) : ℝ)| = ∏ w, |ρ w a| := by sorry
