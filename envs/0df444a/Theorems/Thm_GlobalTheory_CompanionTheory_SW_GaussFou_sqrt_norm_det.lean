-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_GaussFou_sqrt_norm_det
-- name    : GlobalTheory.CompanionTheory.SW.GaussFou.sqrt_norm_det
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:05:26.247801+00:00
-- url     : https://prove2.me/theorems/6d1f4540-fbc5-4a91-8ec6-81711bf36099
-- title:
--   Gauss Fou: sqrt norm det
-- statement:
--   The Gauss Fou construction uses the sqrt norm det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ArchimedeanGaussianFourier.lean#L44-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ArchimedeanGaussianFourier.lean#L44-L50

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

theorem GlobalTheory.CompanionTheory.SW.GaussFou.sqrt_norm_det (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (hF : IsTotallyReal F)
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) :
    Real.sqrt |((Algebra.norm ℚ B.det : ℚ) : ℝ)| = ∏ w, Real.sqrt |(B.map (ρ w)).det| := by sorry
