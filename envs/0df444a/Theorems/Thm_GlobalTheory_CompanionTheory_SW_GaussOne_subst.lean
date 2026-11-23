-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_GaussOne_subst
-- name    : GlobalTheory.CompanionTheory.SW.GaussOne.subst
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:43:16.004058+00:00
-- url     : https://prove2.me/theorems/bf6abf11-0a57-45ac-9c9e-7ac37b02d030
-- title:
--   Gauss One: subst
-- statement:
--   The Gauss One construction uses the subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/RealGaussianFourierTransform.lean#L59-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/RealGaussianFourierTransform.lean#L59-L76

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

theorem GlobalTheory.CompanionTheory.SW.GaussOne.subst (g : Matrix ι ι ℝ) (hg : g.det ≠ 0) (F : (ι → ℝ) → ℂ) (hF : Continuous F) :
    (Integrable (fun u => F (g *ᵥ u)) → Integrable F) ∧
      ∫ u, F (g *ᵥ u) = ((|g.det|⁻¹ : ℝ) : ℂ) * ∫ x, F x := by sorry
