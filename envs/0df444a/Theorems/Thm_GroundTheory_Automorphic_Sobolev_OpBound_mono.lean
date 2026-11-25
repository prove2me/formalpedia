-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_OpBound_mono
-- name    : GroundTheory.Automorphic.Sobolev.OpBound.mono
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T06:06:01.106179+00:00
-- url     : https://prove2.me/theorems/85ad1f92-2e75-4178-90ae-4b27a9eacd7c
-- title:
--   Op Bound: mono
-- statement:
--   The Op Bound construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticLocal.lean#L432-L433
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticLocal.lean#L432-L433

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticLocal
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_HasOrder_mono

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Sobolev
open TemperedDistribution MeasureTheory FourierTransform LineDeriv
open scoped SchwartzMap ENNReal ContDiff
noncomputable section
set_option linter.unusedSectionVars false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
open GroundTheory.Automorphic.Sobolev.OpBound
variable {A B : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)} {s t r C D : ℝ}

theorem GroundTheory.Automorphic.Sobolev.OpBound.mono (hA : OpBound A s t C) (hCD : C ≤ D) : OpBound A s t D := by sorry
