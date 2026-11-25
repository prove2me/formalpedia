-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GL2Classical_mem_of_sum_mem_of_eigen
-- name    : GroundTheory.Automorphic.GL2Classical.mem_of_sum_mem_of_eigen
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:52:45.443179+00:00
-- url     : https://prove2.me/theorems/3e1aaa32-673a-49bb-a1e7-80d81aaa51dd
-- title:
--   GL2 Classical: mem of sum mem of eigen
-- statement:
--   The GL2 Classical construction uses the mem of sum mem of eigen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2Classical/WeightOperators.lean#L76-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2Classical/WeightOperators.lean#L76-L107

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GL2Classical_WeightOperators
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.GL2Classical
variable {E : Type*} [AddCommGroup E] [Module ℂ E] {Rr Ll Jj : Module.End ℂ E}

theorem GroundTheory.Automorphic.GL2Classical.mem_of_sum_mem_of_eigen {W : Submodule ℂ E} (hW : ∀ v ∈ W, Jj v ∈ W) {ι : Type*} [DecidableEq ι]
    (s : Finset ι) : ∀ (v : ι → E) (μ : ι → ℂ), (∀ i ∈ s, Jj (v i) = μ i • v i) → Set.InjOn μ s →
      ∑ i ∈ s, v i ∈ W → ∀ i ∈ s, v i ∈ W := by sorry
