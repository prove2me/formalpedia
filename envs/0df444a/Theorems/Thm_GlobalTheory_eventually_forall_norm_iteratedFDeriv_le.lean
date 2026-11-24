-- Prove2me | Theorems.Thm_GlobalTheory_eventually_forall_norm_iteratedFDeriv_le
-- name    : GlobalTheory.eventually_forall_norm_iteratedFDeriv_le
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:19:46.584416+00:00
-- url     : https://prove2.me/theorems/4fb89307-9d1c-45b3-abd2-d801295d0a1c
-- title:
--   Global Theory: eventually forall norm iterated FDeriv le
-- statement:
--   The Global Theory construction uses the eventually forall norm iterated FDeriv le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzContinuousAtOfPointwiseOfBounded.lean#L110-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzContinuousAtOfPointwiseOfBounded.lean#L110-L155

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzContinuousAtOfPointwiseOfBounded
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory

theorem GlobalTheory.eventually_forall_norm_iteratedFDeriv_le {X V : Type*} {l : Filter X}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {h : X → SchwartzMap V ℂ}
    (hp : ∀ v, Tendsto (fun x => h x v) l (𝓝 0))
    (hb : ∀ k n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x in l, ∀ v, ‖v‖ ^ k * ‖iteratedFDeriv ℝ n (h x) v‖ ≤ C)
    (n : ℕ) : ∀ ε : ℝ, 0 < ε → ∀ᶠ x in l, ∀ v, ‖iteratedFDeriv ℝ n (h x) v‖ ≤ ε := by sorry
