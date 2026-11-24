-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_ThW_GaussFlat_integral_cur
-- name    : GlobalTheory.CompanionTheory.SW.ThW.GaussFlat.integral_cur
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:10:54.622461+00:00
-- url     : https://prove2.me/theorems/9c1b3046-e33e-42bf-a15a-5644b3af34e9
-- title:
--   Gauss Flat: integral cur
-- statement:
--   The Gauss Flat construction uses the integral cur property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GaussianFourierTransformFormula.lean#L43-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GaussianFourierTransformFormula.lean#L43-L45

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

theorem GlobalTheory.CompanionTheory.SW.ThW.GaussFlat.integral_cur (f : (InfinitePlace F → ι → ℝ) → ℂ) :
    ∫ x : ι × InfinitePlace F → ℝ, f (cur x) = ∫ z, f z := by sorry
