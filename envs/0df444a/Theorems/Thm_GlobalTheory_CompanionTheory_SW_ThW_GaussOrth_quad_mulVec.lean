-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_ThW_GaussOrth_quad_mulVec
-- name    : GlobalTheory.CompanionTheory.SW.ThW.GaussOrth.quad_mulVec
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:10:50.013798+00:00
-- url     : https://prove2.me/theorems/5c33f099-b66c-4b2b-8c0a-63972e1788cb
-- title:
--   Gauss Orth: quad mul Vec
-- statement:
--   The Gauss Orth construction uses the quad mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GaussianChangeOfVariablesIsometry.lean#L11-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GaussianChangeOfVariablesIsometry.lean#L11-L15

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

theorem GlobalTheory.CompanionTheory.SW.ThW.GaussOrth.quad_mulVec {ι : Type} [Fintype ι] [DecidableEq ι] (g M : Matrix ι ι ℝ) (x : ι → ℝ) :
    (g *ᵥ x) ⬝ᵥ (M *ᵥ (g *ᵥ x)) = x ⬝ᵥ ((gᵀ * M * g) *ᵥ x) := by sorry
