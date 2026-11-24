-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_GaussOne_lin
-- name    : GlobalTheory.CompanionTheory.SW.GaussOne.lin
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T12:05:18.528303+00:00
-- url     : https://prove2.me/theorems/bd58bb2a-0a46-4f33-8164-b44d39c806bc
-- title:
--   Gauss One: lin
-- statement:
--   The Gauss One construction uses the lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/RealGaussianFourierTransform.lean#L96-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/RealGaussianFourierTransform.lean#L96-L105

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SimultaneousNormalFormMajorant
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_RealGaussianFourierTransform
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.GaussOne
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.CompanionTheory.SW.GaussOne.lin {g S : Matrix ι ι ℝ} {e : ι → ℝ} (hS : gᵀ * S * g = Matrix.diagonal e)
    (u v : ι → ℝ) :
    2 * (Real.pi : ℂ) * Complex.I * (((g *ᵥ u) ⬝ᵥ (S *ᵥ (g *ᵥ v)) : ℝ) : ℂ)
      = ∑ i, (2 * (Real.pi : ℂ) * Complex.I * (e i : ℂ) * (v i : ℂ)) * (u i : ℂ) := by sorry
