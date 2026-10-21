-- Prove2me | Theorems.Thm_MajorityAttack_NegCost_min_attack_power_lt
-- name    : MajorityAttack.NegCost.min_attack_power_lt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:41:10.657965+00:00
-- url     : https://prove2.me/theorems/635fdedf-c70f-43ca-9481-64c21fc44ac0
-- title:
--   Proof of Proposition 1 — positive incumbent power makes the attack bound less than H
-- statement:
--   For total hash power $H>0$ and a miner's positive incumbent power $h^*>0$, the minimum attack-power bound is strictly below the incumbent total:
--
--   $$\max\{H/2,H-h^*\}<H.$$
--
--   This is the feasibility observation in the proof of Proposition 1. It connects a miner with incumbent power to a slower attacking chain.
-- source:
--   Gans & Halaburda, “Zero Cost” Majority Attacks on Permissionless Blockchains, arXiv:2308.06568v1, p. 13, proof of Proposition 1

import Mathlib
import Definitions.Def_MajorityAttack_NegCost_Model

namespace MajorityAttack.NegCost

/-- Proof of Proposition 1, p. 13: positive incumbent power permits attack power below `H`. -/
theorem min_attack_power_lt (H hstar : ℝ) (hH : 0 < H) (hhstar : 0 < hstar) :
    minAttackPower H hstar < H := by sorry

end MajorityAttack.NegCost
