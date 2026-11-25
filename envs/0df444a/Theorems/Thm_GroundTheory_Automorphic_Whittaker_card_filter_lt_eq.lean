-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_card_filter_lt_eq
-- name    : GroundTheory.Automorphic.Whittaker.card_filter_lt_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:40:41.11037+00:00
-- url     : https://prove2.me/theorems/80e459c2-70f4-4995-a5ea-43dc7f059635
-- title:
--   Whittaker: card filter lt eq
-- statement:
--   The Whittaker construction uses the card filter lt eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCells.lean#L237-L247
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCells.lean#L237-L247

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCells
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Matrix DoubleCoset
variable {F : Type*} [Field F] {n : ℕ}

theorem GroundTheory.Automorphic.Whittaker.card_filter_lt_eq (w : Equiv.Perm (Fin n)) (r j : Fin n) :
    (Finset.univ.filter fun x : Fin n => r < x ∧ w⁻¹ x ≤ j).card =
      if h : r.val + 1 < n then llRank ⟨r.val + 1, h⟩ j (permGL F w) else 0 := by sorry
