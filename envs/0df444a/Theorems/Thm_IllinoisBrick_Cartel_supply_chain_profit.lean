-- Prove2me | Theorems.Thm_IllinoisBrick_Cartel_supply_chain_profit
-- name    : IllinoisBrick.Cartel.supply_chain_profit
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T12:42:54.344447+00:00
-- url     : https://prove2.me/theorems/0920a14f-6394-46e6-a792-9ec080deb6a8
-- title:
--   §4.2, p. 15 (PDF 16) — the four profits sum to (a − bQ − c)Q, which is at most 2(a − c)²/(9b) once Q ≥ 2(a − c)/(3b)
-- statement:
--   Assume $0 < b$ and $c < a$.
--
--   1. For every contract structure, all terms $v$ and all quantities $q_1, q_2$, with $Q = q_1 + q_2$,
--   $$\pi_1 + \pi_2 + \Pi_1 + \Pi_2 = (a - bQ - c)\,Q .$$
--   2. For every $Q \ge 2(a-c)/(3b)$,
--   $$(a - bQ - c)\,Q \le \frac{2(a-c)^2}{9b}.$$
--
--   The payments are transfers inside the supply chain, so total profit depends only on the total quantity; and the competitive total $2(a-c)/(3b)$ already exceeds the profit-maximizing total $(a-c)/(2b)$, so any larger total earns less. Raising the wholesale price lowers the retailers' quantities and so raises the supply-chain profit.
-- source:
--   Jain, Hasija, Netessine, Supply chains and antitrust governance, accepted manuscript (Management Science 67(11), 2021; LBS Research Online eprint 1493), p. 15 (PDF 16), §4.2

import Mathlib
import Definitions.Def_IllinoisBrick_Cartel_Model

namespace IllinoisBrick.Cartel

/-- §4.2, p. 15: the payments cancel, so the four firms' profits add up to the supply-chain profit
`(a - b Q - c) Q` of the total quantity `Q = q₁ + q₂`, for any contract, terms and quantities; and
this profit is at most its competitive level `2(a - c)²/(9b)` whenever `Q` is at least the
competitive total `2(a - c)/(3b)`. -/
theorem supply_chain_profit (a b c : ℝ) (h : Standing a b c) :
    (∀ (k : Contract) (v : Fin 2 → Terms) (q : Fin 2 → ℝ),
      retailerProfit a b c k v q 0 + retailerProfit a b c k v q 1 +
          manufacturerProfit a b c k v q 0 + manufacturerProfit a b c k v q 1 =
        (a - b * (q 0 + q 1) - c) * (q 0 + q 1)) ∧
    ∀ Q : ℝ, 2 * (a - c) / (3 * b) ≤ Q → (a - b * Q - c) * Q ≤ 2 * (a - c) ^ 2 / (9 * b) := by sorry

end IllinoisBrick.Cartel
