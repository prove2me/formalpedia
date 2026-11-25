-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_ofSchwartz_sub
-- name    : GroundTheory.Automorphic.Sobolev.ofSchwartz_sub
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:14:08.274786+00:00
-- url     : https://prove2.me/theorems/abbf6c72-508f-5670-be5f-b9037d2f390b
-- title:
--   Sobolev: of Schwartz sub
-- statement:
--   The Sobolev construction uses the of Schwartz sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevMultiplication.lean#L436-L439
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevMultiplication.lean#L436-L439

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevRellich
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevEmbedding
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable (χ : 𝓢(E, ℂ))

theorem GroundTheory.Automorphic.Sobolev.ofSchwartz_sub {s : ℝ} (φ ψ : 𝓢(E, ℂ)) :
    SobolevSpace.ofSchwartz s (φ - ψ) = SobolevSpace.ofSchwartz s φ - SobolevSpace.ofSchwartz s ψ := by sorry
