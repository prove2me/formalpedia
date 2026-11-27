-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_eq_sum_smul_of_range_le_iSup_range
-- name    : GlobalTheory.T.exists_eq_sum_smul_of_range_le_iSup_range
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-27T06:04:40.257726+00:00
-- url     : https://prove2.me/theorems/9dc12608-d225-43a1-8efe-0aa1d8c048fa
-- title:
--   T: exists eq sum smul of range le i Sup range
-- statement:
--   The T construction uses the exists eq sum smul of range le i Sup range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IntertwinerMemISupRangeEqSumSmulStatement.lean#L5-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IntertwinerMemISupRangeEqSumSmulStatement.lean#L5-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntertwinerMemISupRangeEqSumSmul
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntertwinerMemISupRangeEqSumSmulStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_eq_sum_smul_of_range_le_iSup_range : ∀ (G : Type) [Group G] (N X : Type) [AddCommGroup N] [Module ℂ N]
    [AddCommGroup X] [Module ℂ X] (π : Representation ℂ G N) (ρ : Representation ℂ G X),
    (∀ φ : π.IntertwiningMap π, ∃ c : ℂ, φ.toLinearMap = c • LinearMap.id) →
    ∀ (m : ℕ) (φ : Fin m → π.IntertwiningMap ρ), Function.Injective (fun w : Fin m → N => ∑ j, φ j (w j)) →
    ∀ ψ : π.IntertwiningMap ρ, LinearMap.range ψ.toLinearMap ≤ ⨆ j, LinearMap.range (φ j).toLinearMap →
    ∃ c : Fin m → ℂ, ∀ n, ψ n = ∑ j, c j • φ j n := by sorry
