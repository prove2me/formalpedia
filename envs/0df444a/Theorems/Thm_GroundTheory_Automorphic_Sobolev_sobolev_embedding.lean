-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_sobolev_embedding
-- name    : GroundTheory.Automorphic.Sobolev.sobolev_embedding
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:33:36.425799+00:00
-- url     : https://prove2.me/theorems/f4e485eb-5080-4b15-9fb2-065b44b5503f
-- title:
--   Sobolev: sobolev embedding
-- statement:
--   The Sobolev construction uses the sobolev embedding property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevEmbedding.lean#L95-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevEmbedding.lean#L95-L118

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_Sobolev
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevEmbedding
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
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem GroundTheory.Automorphic.Sobolev.sobolev_embedding {s : ℝ} (k : ℕ)
    (hs : (k : ℝ) + (Module.finrank ℝ E : ℝ) / 2 < s) (u : SobolevSpace E F s) :
    ∃ g : E → F, ContDiff ℝ k g ∧
      (∀ i : ℕ, i ≤ k → ∃ C, ∀ x, ‖iteratedFDeriv ℝ i g x‖ ≤ C) ∧
      ∀ φ : 𝓢(E, ℂ), SobolevSpace.toDistribution u φ = ∫ x, φ x • g x := by sorry
