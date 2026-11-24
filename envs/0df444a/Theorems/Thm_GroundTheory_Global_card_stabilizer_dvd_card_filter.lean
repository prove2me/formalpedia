-- Prove2me | Theorems.Thm_GroundTheory_Global_card_stabilizer_dvd_card_filter
-- name    : GroundTheory.Global.card_stabilizer_dvd_card_filter
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:41:06.192222+00:00
-- url     : https://prove2.me/theorems/edd3cede-300b-45f0-94a5-450b35cd31b1
-- title:
--   Global: card stabilizer dvd card filter
-- statement:
--   The Global construction uses the card stabilizer dvd card filter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/Permutation.lean#L60-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/Permutation.lean#L60-L66

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Cyclic
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Permutation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open GroundTheory.GroupCoh MulAction
variable (G : Type*) {X : Type*} [Group G] [MulAction G X]
variable {G}
variable [Fintype G]

theorem GroundTheory.Global.card_stabilizer_dvd_card_filter [DecidableEq X] (p y : X) :
    Nat.card (stabilizer G p) ∣ (Finset.univ.filter fun g : G => g • p = y).card := by sorry
