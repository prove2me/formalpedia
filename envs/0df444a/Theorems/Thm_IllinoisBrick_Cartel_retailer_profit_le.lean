-- Prove2me | Theorems.Thm_IllinoisBrick_Cartel_retailer_profit_le
-- name    : IllinoisBrick.Cartel.retailer_profit_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:42:55.164478+00:00
-- url     : https://prove2.me/theorems/4fb06991-b960-491b-9112-ccc5573d3ca2
-- title:
--   §4.2, p. 15 (PDF 16) — under WP, RS, QD and MOQ every retailer equilibrium gives π_i ≤ b q_i²
-- statement:
--   Assume $0 < b$. Let the contract structure be WP, RS, QD or MOQ, let $v = [v_1, v_2]$ be admissible terms (equal or not), and let $(q_1, q_2)$ be a retailer equilibrium under $v$. Then for $i = 1, 2$
--   $$\pi_i \le b\, q_i^2 .$$
--
--   The retailer's profit is tied to its own quantity: a manufacturer can raise its margin only by lowering the retailer's quantity, and then the retailer's profit falls. This is the paper's statement that under these four contracts "any collusive action leads to an irreversible loss to the retailers". Under WPFF the bound fails by exactly the slotting fee $-f$.
-- source:
--   Jain, Hasija, Netessine, Supply chains and antitrust governance, accepted manuscript (Management Science 67(11), 2021; LBS Research Online eprint 1493), p. 15 (PDF 16), §4.2, and pp. 16–17 (PDF 17–18), §4.4 opening

import Mathlib
import Definitions.Def_IllinoisBrick_Cartel_Model

namespace IllinoisBrick.Cartel

/-- §4.2, p. 15, and §4.4, pp. 16–17: under admissible WP, RS, QD or MOQ terms, at every retailer
equilibrium each retailer's profit is at most `b q_i²` (the retailers cannot be compensated). -/
theorem retailer_profit_le (a b c : ℝ) (hb : 0 < b) (k : Contract) (hk : k ≠ Contract.WPFF)
    (v : Fin 2 → Terms) (hadm : ∀ j, Admissible c k (v j)) (q : Fin 2 → ℝ)
    (hq : IsRetailerEq a b c k v q) :
    ∀ i : Fin 2, retailerProfit a b c k v q i ≤ b * q i ^ 2 := by sorry

end IllinoisBrick.Cartel
