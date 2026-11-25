-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_memLp_two_prod_mul
-- name    : GroundTheory.Automorphic.Sobolev.memLp_two_prod_mul
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:14:51.017209+00:00
-- url     : https://prove2.me/theorems/6dd3fad2-364d-4507-9c4f-630f55a29bf3
-- title:
--   Sobolev: mem Lp two prod mul
-- statement:
--   The Sobolev construction uses the mem Lp two prod mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevRellich.lean#L188-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevRellich.lean#L188-L199

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

theorem GroundTheory.Automorphic.Sobolev.memLp_two_prod_mul (φ : 𝓢(E, ℂ)) (G : Lp ℂ 2 (volume : Measure E)) :
    MemLp (fun p : E × E ↦ φ p.1 * G p.2) 2 ((volume : Measure E).prod volume) := by sorry
