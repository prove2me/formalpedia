-- Prove2me | Theorems.Thm_GroundTheory_Global_card_stabilizer_dvd_sum
-- name    : GroundTheory.Global.card_stabilizer_dvd_sum
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:41:49.103176+00:00
-- url     : https://prove2.me/theorems/72781778-b729-4d4a-a7a2-950329333cbf
-- title:
--   Global: card stabilizer dvd sum
-- statement:
--   The Global construction uses the card stabilizer dvd sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/Permutation.lean#L68-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/Permutation.lean#L68-L76

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

theorem GroundTheory.Global.card_stabilizer_dvd_sum [Finite X] (F : X → ℤ) (p : X) :
    (Nat.card (stabilizer G p) : ℤ) ∣ ∑ g : G, F (g • p) := by sorry
