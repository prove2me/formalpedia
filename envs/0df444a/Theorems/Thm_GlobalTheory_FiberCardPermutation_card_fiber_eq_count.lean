-- Prove2me | Theorems.Thm_GlobalTheory_FiberCardPermutation_card_fiber_eq_count
-- name    : GlobalTheory.FiberCardPermutation.card_fiber_eq_count
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:23:17.471804+00:00
-- url     : https://prove2.me/theorems/7d6c7b73-e588-4ab8-808a-025914a54ee5
-- title:
--   Fiber Card Permutation: card fiber eq count
-- statement:
--   The Fiber Card Permutation construction uses the card fiber eq count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsPermOfOfFnPerm.lean#L5-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsPermOfOfFnPerm.lean#L5-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsPermOfOfFnPerm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.FiberCardPermutation

theorem GlobalTheory.FiberCardPermutation.card_fiber_eq_count {α : Type} [DecidableEq α] {n : ℕ} (v : Fin n → α) (c : α) :
    Fintype.card {i : Fin n // v i = c} = Multiset.count c (List.ofFn v : Multiset α) := by sorry
