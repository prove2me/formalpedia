-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_card_filter_lt_apply
-- name    : GroundTheory.Automorphic.Whittaker.card_filter_lt_apply
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:34:55.873802+00:00
-- url     : https://prove2.me/theorems/d417820f-c0ff-4de6-bdb8-8e02f894de99
-- title:
--   Whittaker: card filter lt apply
-- statement:
--   The Whittaker construction uses the card filter lt apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerRelevance.lean#L114-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerRelevance.lean#L114-L119

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerRelevance
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
open Finset
variable {n : ℕ} {w : Equiv.Perm (Fin n)}

theorem GroundTheory.Automorphic.Whittaker.card_filter_lt_apply (w : Equiv.Perm (Fin n)) (b : Fin n) :
    #(univ.filter fun x : Fin n => w x < w b) = (w b).val := by sorry
