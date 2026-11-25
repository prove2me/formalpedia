-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_rellichOp_apply_ae
-- name    : GroundTheory.Automorphic.Sobolev.rellichOp_apply_ae
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:14:53.667779+00:00
-- url     : https://prove2.me/theorems/9cfee1a3-11e0-4715-b61f-d7d3a6dd22a7
-- title:
--   Sobolev: rellich Op apply ae
-- statement:
--   The Sobolev construction uses the rellich Op apply ae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevRellich.lean#L183-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevRellich.lean#L183-L186

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevInterpolation
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidtKernel
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidtCompact
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevRellich
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Sobolev
open TemperedDistribution MeasureTheory FourierTransform
open scoped SchwartzMap ENNReal ContDiff
noncomputable section
set_option linter.unusedSectionVars false
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {s N : ℝ} (χ : 𝓢(E, ℂ))

theorem GroundTheory.Automorphic.Sobolev.rellichOp_apply_ae (hN : (Module.finrank ℝ E : ℝ) < 2 * N)
    (G : Lp ℂ 2 (volume : Measure E)) :
    rellichOp (s := s) χ hN G =ᵐ[volume] fun ξ ↦ ∫ η, rellichKernel s N χ (ξ, η) * G η := by sorry
