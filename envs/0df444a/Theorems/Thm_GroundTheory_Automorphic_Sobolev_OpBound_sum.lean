-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_OpBound_sum
-- name    : GroundTheory.Automorphic.Sobolev.OpBound.sum
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T06:14:50.713044+00:00
-- url     : https://prove2.me/theorems/1f2bc14a-7f68-4fea-bc59-d03037992858
-- title:
--   Op Bound: sum
-- statement:
--   The Op Bound construction uses the sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticLocal.lean#L438-L448
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticLocal.lean#L438-L448

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticLocal
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_HasOrder_sum
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_IsLocal_sum

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

theorem GroundTheory.Automorphic.Sobolev.OpBound.sum {ι : Type*} (S : Finset ι) {A : ι → 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)} {C : ι → ℝ}
    (hC : ∀ i ∈ S, 0 ≤ C i) (h : ∀ i ∈ S, OpBound (A i) s t (C i)) :
    OpBound (∑ i ∈ S, A i) s t (∑ i ∈ S, C i) := by sorry
