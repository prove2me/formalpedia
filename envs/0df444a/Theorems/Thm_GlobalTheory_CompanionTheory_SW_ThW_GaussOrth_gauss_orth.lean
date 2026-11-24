-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_ThW_GaussOrth_gauss_orth
-- name    : GlobalTheory.CompanionTheory.SW.ThW.GaussOrth.gauss_orth
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:11:05.578794+00:00
-- url     : https://prove2.me/theorems/44a998eb-d4fb-41f0-b44b-c3c8b0962030
-- title:
--   Gauss Orth: gauss orth
-- statement:
--   The Gauss Orth construction uses the gauss orth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GaussianChangeOfVariablesIsometry.lean#L67-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GaussianChangeOfVariablesIsometry.lean#L67-L100

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SumRhoEqTrace
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GaussianChangeOfVariablesIsometry
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.ThW GlobalTheory.CompanionTheory.SW.ThW.GaussOrth
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker

theorem GlobalTheory.CompanionTheory.SW.ThW.GaussOrth.gauss_orth {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ)
    (gi : InfinitePlace F → Matrix ι ι ℝ) (hB : B.det ≠ 0)
    (hg : ∀ w, (gi w)ᵀ * B.map (ρ w) * gi w = B.map (ρ w)) :
    (∀ (τ : InfinitePlace F → ℂ) (x : InfinitePlace F → ι → ℝ),
      gauss B ρ P τ (fun w => gi w *ᵥ x w) = gauss B ρ (fun w => (gi w)ᵀ * P w * gi w) τ x) ∧
    ∀ τ : InfinitePlace F → ℂ, cG B ρ (fun w => (gi w)ᵀ * P w * gi w) τ = cG B ρ P τ := by sorry
