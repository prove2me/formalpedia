-- Prove2me | Theorems.Thm_GlobalTheory_T_eq_sum_prod_of_expansion_in_each_coordinate
-- name    : GlobalTheory.T.eq_sum_prod_of_expansion_in_each_coordinate
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:27:54.568156+00:00
-- url     : https://prove2.me/theorems/0194c12e-4f84-57cf-8adc-e4e68907ce1a
-- title:
--   T: eq sum prod of expansion in each coordinate
-- statement:
--   The T construction uses the eq sum prod of expansion in each coordinate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExpandPiOfExpandEachStatement.lean#L5-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExpandPiOfExpandEachStatement.lean#L5-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExpandPiOfExpandEach
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExpandPiOfExpandEachStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.eq_sum_prod_of_expansion_in_each_coordinate : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type} (K : ∀ i, Set (X i)) (m : ι → ℕ)
    (k : ∀ i, Fin (m i) → X i) (hk : ∀ i j, k i j ∈ K i) (c : ∀ i, Fin (m i) → X i → ℂ)
    (f : (∀ i, X i) → ℂ)
    (hf : ∀ i (g : ∀ i, X i), (∀ i, g i ∈ K i) → f g = ∑ j, f (Function.update g i (k i j)) * c i j (g i))
    (g : ∀ i, X i) (hg : ∀ i, g i ∈ K i), f g = ∑ J : (∀ i, Fin (m i)), f (fun i => k i (J i)) * ∏ i, c i (J i) (g i) := by sorry
