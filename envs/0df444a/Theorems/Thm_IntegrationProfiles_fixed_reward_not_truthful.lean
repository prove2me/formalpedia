-- Prove2me | Theorems.Thm_IntegrationProfiles_fixed_reward_not_truthful
-- name    : IntegrationProfiles.fixed_reward_not_truthful
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:24:56.906398+00:00
-- url     : https://prove2.me/theorems/319ddb34-b03a-478f-9df0-d71653b55439
-- title:
--   Integration Profiles: fixed reward not truthful
-- statement:
--   SergeevDmitry's example: reward 100, reserve 100, cost 60, one earlier bid of 50.
--       Bidding the true cost loses; bidding 40 wins and earns 40.
--
--   Source: https://github.com/shentonyan/sealed-bid-award-erc/blob/0d615b2e310cdd85d453c8935c1e3bf7a0a41079/IntegrationProfiles.lean#L38-L40
-- source:
--   https://github.com/shentonyan/sealed-bid-award-erc/blob/0d615b2e310cdd85d453c8935c1e3bf7a0a41079/IntegrationProfiles.lean#L38-L40

import Definitions.Def_IntegrationProfiles
set_option autoImplicit true
open IntegrationProfiles

theorem IntegrationProfiles.fixed_reward_not_truthful :
    fixedRewardUtility 100 100 [50] [] 60 40 > fixedRewardUtility 100 100 [50] [] 60 60 := by sorry
