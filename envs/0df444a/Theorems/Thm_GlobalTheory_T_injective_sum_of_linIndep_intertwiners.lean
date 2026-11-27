-- Prove2me | Theorems.Thm_GlobalTheory_T_injective_sum_of_linIndep_intertwiners
-- name    : GlobalTheory.T.injective_sum_of_linIndep_intertwiners
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-27T06:03:04.352058+00:00
-- url     : https://prove2.me/theorems/ec0b78e7-76d9-5200-a59c-d19a5eaa16e6
-- title:
--   T: injective sum of lin Indep intertwiners
-- statement:
--   The T construction uses the injective sum of lin Indep intertwiners property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/InjectiveSumOfLinIndepIntertwinersStatement.lean#L5-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/InjectiveSumOfLinIndepIntertwinersStatement.lean#L5-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_InjectiveSumOfLinIndepIntertwiners
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_InjectiveSumOfLinIndepIntertwinersStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.injective_sum_of_linIndep_intertwiners : ∀ (G : Type) [Group G] (N X : Type) [AddCommGroup N] [Module ℂ N]
    [AddCommGroup X] [Module ℂ X] (π : Representation ℂ G N) (ρ : Representation ℂ G X), π.IsIrreducible →
    (∀ φ : π.IntertwiningMap π, ∃ c : ℂ, φ.toLinearMap = c • LinearMap.id) →
    ∀ (m : ℕ) (φ : Fin m → π.IntertwiningMap ρ), LinearIndependent ℂ φ →
    Function.Injective (fun w : Fin m → N => ∑ j, φ j (w j)) := by sorry
