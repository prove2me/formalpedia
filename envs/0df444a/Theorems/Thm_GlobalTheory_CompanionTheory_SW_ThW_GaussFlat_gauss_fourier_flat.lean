-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_ThW_GaussFlat_gauss_fourier_flat
-- name    : GlobalTheory.CompanionTheory.SW.ThW.GaussFlat.gauss_fourier_flat
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:11:12.426148+00:00
-- url     : https://prove2.me/theorems/3265d656-4b9b-4c4e-a5ad-7cd5249c7525
-- title:
--   Gauss Flat: gauss fourier flat
-- statement:
--   The Gauss Flat construction uses the gauss fourier flat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GaussianFourierTransformFormula.lean#L62-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GaussianFourierTransformFormula.lean#L62-L67

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SumRhoEqTrace
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ArchimedeanGaussianFourier
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GaussianFourierTransformFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.ThW GlobalTheory.CompanionTheory.SW.ThW.GaussFlat
variable {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.CompanionTheory.SW.ThW.GaussFlat.gauss_fourier_flat : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι] [DecidableEq (InfinitePlace F)] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → ∀ τ : InfinitePlace F → ℂ, (∀ w, 0 < (τ w).im) → ∀ y : ι × InfinitePlace F → ℝ, ((Real.sqrt |((Algebra.norm ℚ B.det : ℚ) : ℝ)| : ℝ) : ℂ) * ∫ x : ι × InfinitePlace F → ℝ, gauss B ρ P τ (cur x) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((x ⬝ᵥ (DM B ρ *ᵥ y) : ℝ) : ℂ)) = cG B ρ P τ * gauss B ρ P (fun w => -(τ w)⁻¹) (cur y) := by sorry
