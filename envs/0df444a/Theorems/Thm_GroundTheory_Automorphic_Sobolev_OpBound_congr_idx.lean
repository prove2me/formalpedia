-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_OpBound_congr_idx
-- name    : GroundTheory.Automorphic.Sobolev.OpBound.congr_idx
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:19:43.865973+00:00
-- url     : https://prove2.me/theorems/4c9169da-51bc-4815-ba43-491875e9bc1c
-- title:
--   Op Bound: congr idx
-- statement:
--   The Op Bound construction uses the congr idx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticLocal.lean#L435-L436
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticLocal.lean#L435-L436

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticLocal
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

theorem GroundTheory.Automorphic.Sobolev.OpBound.congr_idx (hA : OpBound A s t C) {s' t' : ℝ} (hs : s' = s) (ht : t' = t) :
    OpBound A s' t' C := by sorry
