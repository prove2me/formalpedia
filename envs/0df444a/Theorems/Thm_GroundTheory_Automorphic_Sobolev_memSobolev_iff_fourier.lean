-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_memSobolev_iff_fourier
-- name    : GroundTheory.Automorphic.Sobolev.memSobolev_iff_fourier
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:15:16.060951+00:00
-- url     : https://prove2.me/theorems/c4cd5c15-11e1-41f1-b111-81e4c70ee5e3
-- title:
--   Sobolev: mem Sobolev iff fourier
-- statement:
--   The Sobolev construction uses the mem Sobolev iff fourier property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/Sobolev.lean#L387-L407
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/Sobolev.lean#L387-L407

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

theorem GroundTheory.Automorphic.Sobolev.memSobolev_iff_fourier {s : ℝ} (u : 𝓢'(E, F)) :
    MemSobolev s 2 u ↔ ∃ g : E → F, MemLp (fun ξ ↦ weight s ξ • g ξ) 2 (volume : Measure E) ∧
      ∀ φ : 𝓢(E, ℂ), 𝓕 u φ = ∫ ξ, φ ξ • g ξ := by sorry
