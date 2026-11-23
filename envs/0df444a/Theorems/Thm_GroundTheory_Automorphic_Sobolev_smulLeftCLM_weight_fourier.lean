-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_smulLeftCLM_weight_fourier
-- name    : GroundTheory.Automorphic.Sobolev.smulLeftCLM_weight_fourier
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:48:13.210924+00:00
-- url     : https://prove2.me/theorems/96567f04-bedd-4435-ac1e-3d1868bcfcae
-- title:
--   Sobolev: smul Left CLM weight fourier
-- statement:
--   The Sobolev construction uses the smul Left CLM weight fourier property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/Sobolev.lean#L345-L349
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/Sobolev.lean#L345-L349

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_Sobolev
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
variable {m : E → ℂ} {C s t : ℝ}

theorem GroundTheory.Automorphic.Sobolev.smulLeftCLM_weight_fourier {s : ℝ} (u : SobolevSpace E F s) :
    smulLeftCLM F (weight s) (𝓕 (SobolevSpace.toDistribution u)) =
      ((𝓕 (SobolevSpace.bessel s u) : Lp F 2 (volume : Measure E)) : 𝓢'(E, F)) := by sorry
