-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_ThetaUD_gauss_sq
-- name    : GlobalTheory.CompanionTheory.SW.ThetaUD.gauss_sq
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:11:17.403805+00:00
-- url     : https://prove2.me/theorems/0aa4644b-4242-419d-bbdb-f30534104a3a
-- title:
--   Theta UD: gauss sq
-- statement:
--   The Theta UD construction uses the gauss sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ThetaFunctionModularity.lean#L61-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ThetaFunctionModularity.lean#L61-L74

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ThetaFunctionModularity
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.ThetaUD
variable {F : Type} [Field F] [NumberField F]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.CompanionTheory.SW.ThetaUD.gauss_sq (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ)
    (τ : InfinitePlace F → ℂ) (c : InfinitePlace F → ℝ) (y : InfinitePlace F → ι → ℝ) :
    gauss B ρ P (fun w => ((c w : ℝ) : ℂ) ^ 2 * τ w) y = gauss B ρ P τ (fun w => c w • y w) := by sorry
