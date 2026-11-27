-- Prove2me | Theorems.Thm_GlobalTheory_OrthogonalProjectionOnto_main
-- name    : GlobalTheory.OrthogonalProjectionOnto.main
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-27T05:54:53.89294+00:00
-- url     : https://prove2.me/theorems/efa715ab-d585-59eb-92c8-0bce277bd02d
-- title:
--   Orthogonal Projection Onto: main
-- statement:
--   The Orthogonal Projection Onto construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/EndoApplyEq.lean#L42-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/EndoApplyEq.lean#L42-L58

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EndoApplyEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2 u_3
open GlobalTheory GlobalTheory.OrthogonalProjectionOnto
open Module

theorem GlobalTheory.OrthogonalProjectionOnto.main : ∀ {R : Type u_1} [inst : Ring R] {ι : Type u_2} [Fintype ι] [inst_2 : DecidableEq ι]
    (M : ι → Type u_3) [inst_3 : (i : ι) → AddCommGroup (M i)] [inst_4 : (i : ι) → Module R (M i)]
    [∀ (i : ι), IsSimpleModule R (M i)],
    (∀ (i j : ι), i ≠ j → ∀ (f : M i →ₗ[R] M j), f = (0 : M i →ₗ[R] M j)) →
    ∀ (i₀ : ι) (s : (i : ι) → Finset (M i)), ∃ (r : R), ∀ (i : ι), ∀ m ∈ s i,
      r • m = if i = i₀ then m else (0 : M i) := by sorry
