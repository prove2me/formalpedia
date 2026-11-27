-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_rellich
-- name    : GroundTheory.Automorphic.Sobolev.rellich
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:59:07.820314+00:00
-- url     : https://prove2.me/theorems/0eb98621-44ac-5832-a239-c6a6201349bf
-- title:
--   Sobolev: rellich
-- statement:
--   The Sobolev construction uses the rellich property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevRellich.lean#L267-L342
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevRellich.lean#L267-L342

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
open Filter Topology

theorem GroundTheory.Automorphic.Sobolev.rellich {s t : ℝ} (hts : t < s) {K : Set E} (hK : IsCompact K)
    (u : ℕ → SobolevSpace E ℂ s) {M : ℝ} (hM : ∀ j, ‖u j‖ ≤ M)
    (hsupp : ∀ j, Distribution.IsVanishingOn (SobolevSpace.toDistribution (u j)) Kᶜ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : SobolevSpace E ℂ t,
      Tendsto (fun j ↦ SobolevSpace.inclusion hts.le (u (φ j))) atTop (𝓝 v) := by sorry
