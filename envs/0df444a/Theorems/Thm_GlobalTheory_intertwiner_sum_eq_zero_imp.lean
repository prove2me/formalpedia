-- Prove2me | Theorems.Thm_GlobalTheory_intertwiner_sum_eq_zero_imp
-- name    : GlobalTheory.intertwiner_sum_eq_zero_imp
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-27T06:03:41.710835+00:00
-- url     : https://prove2.me/theorems/82a6c5bb-e352-48cd-8d72-f91ac1cbe51a
-- title:
--   Global Theory: intertwiner sum eq zero imp
-- statement:
--   The Global Theory construction uses the intertwiner sum eq zero imp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/InjectiveSumOfLinIndepIntertwiners.lean#L7-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/InjectiveSumOfLinIndepIntertwiners.lean#L7-L100

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_InjectiveSumOfLinIndepIntertwiners
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Representation

theorem GlobalTheory.intertwiner_sum_eq_zero_imp {G : Type} [Group G] {N X : Type} [AddCommGroup N] [Module ℂ N]
    [AddCommGroup X] [Module ℂ X] (π : Representation ℂ G N) (ρ : Representation ℂ G X)
    (hirr : π.IsIrreducible)
    (hschur : ∀ φ : π.IntertwiningMap π, ∃ c : ℂ, φ.toLinearMap = c • LinearMap.id) :
    ∀ (m : ℕ) (φ : Fin m → π.IntertwiningMap ρ), LinearIndependent ℂ φ →
      ∀ w : Fin m → N, ∑ j, φ j (w j) = 0 → w = 0 := by sorry
