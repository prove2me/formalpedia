-- Prove2me | Theorems.Thm_GlobalTheory_tendstoLocallyUniformly_sum_smul_const
-- name    : GlobalTheory.tendstoLocallyUniformly_sum_smul_const
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:22:23.008525+00:00
-- url     : https://prove2.me/theorems/7adc8c03-ceb5-46e4-aa30-6e57d4c678fb
-- title:
--   Global Theory: tendsto Locally Uniformly sum smul const
-- statement:
--   The Global Theory construction uses the tendsto Locally Uniformly sum smul const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/DifferentiableAtLimitOfDirectionalDerivsConverge.lean#L9-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/DifferentiableAtLimitOfDirectionalDerivsConverge.lean#L9-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_DifferentiableAtLimitOfDirectionalDerivsConverge
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff Topology
open GlobalTheory
open Filter

theorem GlobalTheory.tendstoLocallyUniformly_sum_smul_const {E : Type} [TopologicalSpace E] {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℂ F] {A : Type} (s : Finset A) (L : A → F)
    (f : A → ℕ → E → ℂ) (ψ : A → E → ℂ)
    (h : ∀ a, TendstoLocallyUniformly (f a) (ψ a) atTop) :
    TendstoLocallyUniformly (fun j y => ∑ a ∈ s, f a j y • L a)
      (fun y => ∑ a ∈ s, ψ a y • L a) atTop := by sorry
