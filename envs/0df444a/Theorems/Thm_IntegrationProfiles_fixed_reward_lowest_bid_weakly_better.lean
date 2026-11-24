-- Prove2me | Theorems.Thm_IntegrationProfiles_fixed_reward_lowest_bid_weakly_better
-- name    : IntegrationProfiles.fixed_reward_lowest_bid_weakly_better
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:24:57.489027+00:00
-- url     : https://prove2.me/theorems/1c6ecdfa-862e-4744-aac8-68a5ae2efbb3
-- title:
--   Integration Profiles: fixed reward lowest bid weakly better
-- statement:
--   More generally: with a fixed reward, any bidder whose cost is below the reward weakly
--       prefers the lowest possible bid to its true cost. Bidding lower never loses a win.
--
--   Source: https://github.com/shentonyan/sealed-bid-award-erc/blob/0d615b2e310cdd85d453c8935c1e3bf7a0a41079/IntegrationProfiles.lean#L44-L58
-- source:
--   https://github.com/shentonyan/sealed-bid-award-erc/blob/0d615b2e310cdd85d453c8935c1e3bf7a0a41079/IntegrationProfiles.lean#L44-L58

import Definitions.Def_IntegrationProfiles
set_option autoImplicit true
open IntegrationProfiles

theorem IntegrationProfiles.fixed_reward_lowest_bid_weakly_better (reward r : Nat) (before after : List Nat) (c : Nat)
    (hc : c ≤ reward) :
    fixedRewardUtility reward r before after c c ≤ fixedRewardUtility reward r before after c 0 := by sorry
