-- Prove2me | Theorems.Thm_MajorityAttack_NegCost_not_binding
-- name    : MajorityAttack.NegCost.not_binding
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T12:41:11.270813+00:00
-- url     : https://prove2.me/theorems/3b84f389-8533-4063-9b94-cb5b2dc67bde
-- title:
--   §4.2 — a nonbinding attack-power constraint gives negative net cost
-- statement:
--   Suppose block rewards on the attacking chain satisfy $\widetilde\rho>\rho$. Let $\widetilde h_A$ maximize attack-chain flow profit over nonnegative hash powers, and suppose the attack-power lower bound does not bind, $h_A\le\widetilde h_A$. If the miner's incumbent power $h^*>0$, the block interval $\tau$, total power $H$, and expected attack duration $\mathcal L$ are positive, then
--
--   $$C_{\rm net}(h^*,\widetilde h_A)<0.$$
--
--   This is the nonbinding case of the cost comparison in §4.2. It identifies when an attack is attractive even without a private gain from changing the transaction record.
-- source:
--   Gans & Halaburda, “Zero Cost” Majority Attacks on Permissionless Blockchains, arXiv:2308.06568v1, p. 10, §4.2, paragraph beginning “When the mining rewards are higher”

import Mathlib
import Definitions.Def_MajorityAttack_NegCost_Model

namespace MajorityAttack.NegCost

/-- Section 4.2, p. 10: when the lower bound does not bind, higher attack-chain rewards
make the net attack cost strictly negative. -/
theorem not_binding (τ H L ρ ρt : ℝ) (c : ℝ → ℝ) (htil hstar : ℝ)
    (hτ : 0 < τ) (hH : 0 < H) (hL : 0 < L) (hreward : ρ < ρt)
    (hopt : IsAttackOptimum (τ * H) ρt c htil)
    (hhstar : 0 < hstar) (hbound : minAttackPower H hstar ≤ htil) :
    netCost τ H L ρ ρt c htil hstar < 0 := by sorry

end MajorityAttack.NegCost
